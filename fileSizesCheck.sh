#!/bin/bash
set -euo pipefail

# Reports:
#   - Oversized files (tables) for JS/MJS, SYS2, Markdown with file sizes in KB
#   - Total line counts and sizes by extension
#   - Line length warnings for terminal visibility
#
# This is meant to quickly spot files that violate the code-size style guide.

YELLOW_THRESHOLD=500
RED_THRESHOLD=800
LONG_LINE_THRESHOLD=120
VERY_LONG_LINE_THRESHOLD=150

# Color definitions
if [[ -t 1 ]]; then
  COLOR_RED=$(tput setaf 1 2>/dev/null || true)
  COLOR_YELLOW=$(tput setaf 3 2>/dev/null || true)
  COLOR_GREEN=$(tput setaf 2 2>/dev/null || true)
  COLOR_CYAN=$(tput setaf 6 2>/dev/null || true)
  COLOR_RESET=$(tput sgr0 2>/dev/null || true)
else
  COLOR_RED=""
  COLOR_YELLOW=""
  COLOR_GREEN=""
  COLOR_CYAN=""
  COLOR_RESET=""
fi

TERM_COLS=$(tput cols 2>/dev/null || echo "${COLUMNS:-80}")

shorten_path() {
  local p="$1"
  local max="$2"
  local len=${#p}
  if (( len <= max || max <= 4 )); then
    printf "%s" "$p"
    return
  fi
  local keep=$((max - 1))
  if (( keep < 1 )); then keep=1; fi
  printf "…%s" "${p: -keep}"
}

colorize_count() {
  local count="$1"
  local padded="$2"

  if [[ -z "$COLOR_RESET" ]]; then
    printf "%s" "$padded"
    return
  fi

  if (( count > RED_THRESHOLD )); then
    printf "%s%s%s" "$COLOR_RED" "$padded" "$COLOR_RESET"
    return
  fi
  if (( count > YELLOW_THRESHOLD )); then
    printf "%s%s%s" "$COLOR_YELLOW" "$padded" "$COLOR_RESET"
    return
  fi
  printf "%s" "$padded"
}

get_file_size_kb() {
  local file="$1"
  local size_bytes
  size_bytes=$(stat -f%z "$file" 2>/dev/null || stat -c%s "$file" 2>/dev/null)
  local size_kb=$((size_bytes / 1024))
  if [ $size_kb -eq 0 ]; then
    size_kb=1  # Show at least 1KB for small files
  fi
  echo $size_kb
}

compute_total_lines() {
  local -n files_ref="$1"
  if (( ${#files_ref[@]} == 0 )); then
    echo 0
    return
  fi
  printf '%s\0' "${files_ref[@]}" | xargs -0 wc -l | tail -n 1 | awk '{print $1}'
}

compute_total_size_kb() {
  local -n files_ref="$1"
  local total_kb=0
  for file in "${files_ref[@]}"; do
    local size_kb
    size_kb=$(get_file_size_kb "$file")
    total_kb=$((total_kb + size_kb))
  done
  echo $total_kb
}

check_very_long_lines() {
  local file="$1"
  local very_long_lines
  local avg_length
  local first_line
  very_long_lines=$(awk 'length($0) > 300 {count++} END {print count+0}' "$file")
  avg_length=$(awk 'length($0) > 300 {total += length($0); count++} END {if (count > 0) print int(total/count); else print 0}' "$file")
  first_line=$(awk 'length($0) > 300 {print NR; exit}' "$file")
  if [ -z "$first_line" ]; then first_line=0; fi
  echo "$very_long_lines $avg_length $first_line"
}

oversized_rows() {
  local min_lines="$1"
  local -n files_ref="$2"

  if (( ${#files_ref[@]} == 0 )); then
    return 0
  fi

  # wc format: "<lines> <path>", final line is the total which we drop.
  printf '%s\0' "${files_ref[@]}" | xargs -0 wc -l | sed '$d' | awk -v min="$min_lines" '$1 > min { print }'
}

render_oversized_table() {
  local title="$1"
  local min_lines="$2"
  local array_name="$3"
  local -n files_ref="$array_name"

  local -a rows=()
  mapfile -t rows < <(oversized_rows "$min_lines" "$array_name" | sort -nr)

  echo "--- ${title} oversized files (>${min_lines} lines) ---"

  local count=${#rows[@]}
  if (( count == 0 )); then
    echo "(none)"
    echo ""
    return
  fi

  local col_lines=7
  local col_size=8
  local col_level=6
  local col_warn150=8
  local col_path=$((TERM_COLS - col_lines - col_size - col_level - col_warn150 - 12))
  if (( col_path < 25 )); then col_path=25; fi

  printf "%-${col_lines}s | %-${col_size}s | %-${col_level}s | %-${col_warn150}s | %s\n" "Lines" "Size(KB)" "Level" ">300chr" "Path"
  printf "%-${col_lines}s-+-%-${col_size}s-+-%-${col_level}s-+-%-${col_warn150}s-+-%s\n" \
    "$(printf '%*s' "$col_lines" | tr ' ' '-')" \
    "$(printf '%*s' "$col_size" | tr ' ' '-')" \
    "$(printf '%*s' "$col_level" | tr ' ' '-')" \
    "$(printf '%*s' "$col_warn150" | tr ' ' '-')" \
    "$(printf '%*s' "$col_path" | tr ' ' '-')"

  for entry in "${rows[@]}"; do
    local line_count file_path
    line_count=$(awk '{print $1}' <<<"$entry")
    file_path=$(awk '{ $1=""; sub(/^ +/,""); print }' <<<"$entry")

    local level="WARN"
    if (( line_count > RED_THRESHOLD )); then
      level="RED"
    fi

    local size_kb
    size_kb=$(get_file_size_kb "$file_path")
    
    local warn150_col=""
    if [[ "$file_path" == *.md ]]; then
      local long_info
      long_info=$(check_very_long_lines "$file_path")
      local very_long_lines avg_length first_line
      very_long_lines=$(echo "$long_info" | cut -d' ' -f1)
      avg_length=$(echo "$long_info" | cut -d' ' -f2)
      first_line=$(echo "$long_info" | cut -d' ' -f3)
      
      if (( very_long_lines > 0 )); then
        warn150_col="${COLOR_RED}${very_long_lines}${COLOR_RESET}"
      else
        warn150_col="${COLOR_GREEN}0${COLOR_RESET}"
      fi
    else
      warn150_col="N/A"
    fi

    local display_path
    display_path=$(shorten_path "$file_path" "$col_path")

    local num_padded
    printf -v num_padded "%6s" "$line_count"
    num_padded=$(colorize_count "$line_count" "$num_padded")
    
    printf "%-${col_lines}s | %7s | %-${col_level}s | %7s | %s\n" "$num_padded" "${size_kb}" "$level" "$warn150_col" "$display_path"
  done

  echo ""
}

# Calculate project size
echo "=== VSAVM Project File Analysis ==="
echo
echo "📊 PROJECT SIZE ANALYSIS"
echo "========================"
total_project_size=$(du -sk . 2>/dev/null | cut -f1)
echo "Total project size: ${total_project_size} KB ($(echo "scale=1; $total_project_size/1024" | bc -l 2>/dev/null || echo "$(($total_project_size/1024))") MB)"

if [ -d "docs" ]; then
    docs_size=$(du -sk docs 2>/dev/null | cut -f1)
    echo "Documentation size: ${docs_size} KB ($(echo "scale=1; $docs_size/1024" | bc -l 2>/dev/null || echo "$(($docs_size/1024))") MB)"
fi

if [ -d "docs/specs" ]; then
    specs_size=$(du -sk docs/specs 2>/dev/null | cut -f1)
    echo "Specifications size: ${specs_size} KB ($(echo "scale=1; $specs_size/1024" | bc -l 2>/dev/null || echo "$(($specs_size/1024))") MB)"
fi
echo

files_to_process=()
while IFS= read -r -d '' file; do
  files_to_process+=("$file")
done < <(
  find . -path "*/node_modules" -prune -o -type f \( -name "*.js" -o -name "*.mjs" -o -name "*.sys2" -o -name "*.md" -o -name "*.html" -o -name "*.css" \) -print0
)

if (( ${#files_to_process[@]} == 0 )); then
  echo "No JS/MJS/SYS2/MD/HTML/CSS files found."
  exit 0
fi

js_files=()
mjs_files=()
jsmjs_files=()
sys2_files=()
md_files=()
html_files=()
css_files=()

for file in "${files_to_process[@]}"; do
  case "$file" in
    *.js) js_files+=("$file"); jsmjs_files+=("$file") ;;
    *.mjs) mjs_files+=("$file"); jsmjs_files+=("$file") ;;
    *.sys2) sys2_files+=("$file") ;;
    *.md) md_files+=("$file") ;;
    *.html) html_files+=("$file") ;;
    *.css) css_files+=("$file") ;;
  esac
done

total_js_lines=$(compute_total_lines js_files)
total_mjs_lines=$(compute_total_lines mjs_files)
total_sys2_lines=$(compute_total_lines sys2_files)
total_md_lines=$(compute_total_lines md_files)
total_html_lines=$(compute_total_lines html_files)
total_css_lines=$(compute_total_lines css_files)

total_js_size=$(compute_total_size_kb js_files)
total_mjs_size=$(compute_total_size_kb mjs_files)
total_sys2_size=$(compute_total_size_kb sys2_files)
total_md_size=$(compute_total_size_kb md_files)
total_html_size=$(compute_total_size_kb html_files)
total_css_size=$(compute_total_size_kb css_files)

echo "--- Oversized Files ---"
render_oversized_table "JS/MJS" "$YELLOW_THRESHOLD" jsmjs_files
render_oversized_table "SYS2" "$YELLOW_THRESHOLD" sys2_files
render_oversized_table "Markdown" "$YELLOW_THRESHOLD" md_files
render_oversized_table "HTML" "$YELLOW_THRESHOLD" html_files
render_oversized_table "CSS" "$YELLOW_THRESHOLD" css_files

total_all_lines=$((total_js_lines + total_mjs_lines + total_sys2_lines + total_md_lines + total_html_lines + total_css_lines))
total_all_size=$((total_js_size + total_mjs_size + total_sys2_size + total_md_size + total_html_size + total_css_size))

echo "--- Line Totals and File Sizes ---"
printf "%-8s | %-6s | %-8s | %-8s | %s\n" "Type" "Files" "Lines" "Size(KB)" "Avg KB/File"
printf "%-8s-+-%-6s-+-%-8s-+-%-8s-+-%s\n" "--------" "------" "--------" "--------" "----------"
printf "%-8s | %6d | %8s | %8s | %s\n" ".js" "${#js_files[@]}" "$total_js_lines" "$total_js_size" "$(( ${#js_files[@]} > 0 ? total_js_size / ${#js_files[@]} : 0 ))"
printf "%-8s | %6d | %8s | %8s | %s\n" ".mjs" "${#mjs_files[@]}" "$total_mjs_lines" "$total_mjs_size" "$(( ${#mjs_files[@]} > 0 ? total_mjs_size / ${#mjs_files[@]} : 0 ))"
printf "%-8s | %6d | %8s | %8s | %s\n" ".sys2" "${#sys2_files[@]}" "$total_sys2_lines" "$total_sys2_size" "$(( ${#sys2_files[@]} > 0 ? total_sys2_size / ${#sys2_files[@]} : 0 ))"
printf "%-8s | %6d | %8s | %8s | %s\n" ".md" "${#md_files[@]}" "$total_md_lines" "$total_md_size" "$(( ${#md_files[@]} > 0 ? total_md_size / ${#md_files[@]} : 0 ))"
printf "%-8s | %6d | %8s | %8s | %s\n" ".html" "${#html_files[@]}" "$total_html_lines" "$total_html_size" "$(( ${#html_files[@]} > 0 ? total_html_size / ${#html_files[@]} : 0 ))"
printf "%-8s | %6d | %8s | %8s | %s\n" ".css" "${#css_files[@]}" "$total_css_lines" "$total_css_size" "$(( ${#css_files[@]} > 0 ? total_css_size / ${#css_files[@]} : 0 ))"
printf "%-8s | %6s | %8s | %8s | %s\n" "TOTAL" "-" "$total_all_lines" "$total_all_size" "-"
echo ""

# Line length analysis for markdown files
total_very_long_lines=0
for file in "${md_files[@]}"; do
  long_info=$(check_very_long_lines "$file")
  very_long_lines=$(echo "$long_info" | cut -d' ' -f1)
  total_very_long_lines=$((total_very_long_lines + very_long_lines))
done

echo "📋 MARKDOWN LINE LENGTH ANALYSIS"
echo "================================="
echo "Total markdown files: ${#md_files[@]}"
echo "${COLOR_RED}Files with lines >300 chars (ridiculously long): ${total_very_long_lines} lines${COLOR_RESET}"
echo ""
echo "📄 FILES WITH LINES >300 CHARACTERS:"
echo "File                                     | Count | Avg Length | First Line"
echo "-----------------------------------------+-------+------------+-----------"
for file in "${md_files[@]}"; do
  long_info=$(check_very_long_lines "$file")
  very_long_lines=$(echo "$long_info" | cut -d' ' -f1)
  avg_length=$(echo "$long_info" | cut -d' ' -f2)
  first_line=$(echo "$long_info" | cut -d' ' -f3)
  
  if (( very_long_lines > 0 )); then
    filename=$(basename "$file")
    # Format numbers with proper alignment
    col1=$(printf "%5d" "$very_long_lines")
    col2=$(printf "%7d" "$avg_length")
    col3=$(printf "%7d" "$first_line")
    
    # Apply colors
    col1="${COLOR_RED}${col1}${COLOR_RESET}"
    col2="${COLOR_YELLOW}${col2}${COLOR_RESET}"
    col3="${COLOR_CYAN}${col3}${COLOR_RESET}"
    
    printf "%-40s | %s | %s chars | line %s\n" "$filename" "$col1" "$col2" "$col3"
  fi
done
echo ""
echo "💡 Note: Only showing files with lines >300 characters"
echo "   Count = number of lines exceeding 300 chars"
echo "   Avg Length = average character count of those long lines"
echo "   First Line = line number of first violation (for quick navigation)"

if [ "$total_very_long_lines" -eq 0 ]; then
    echo "✅ All markdown lines are under 150 characters"
elif [ "$total_very_long_lines" -lt 50 ]; then
    echo "⚠️  Few long lines - minor readability issues"
elif [ "$total_very_long_lines" -lt 200 ]; then
    echo "🚨 Many long lines - significant readability issues"
else
    echo "🔥 CRITICAL: Too many long lines - major readability problems"
fi
echo ""
