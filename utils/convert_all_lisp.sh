#!/bin/bash
# Convert all .lisp files in a directory to .ipynb notebooks

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
CONVERTER="$SCRIPT_DIR/lisp_to_ipynb.py"

# Function to show usage
usage() {
    echo "Usage: $0 [directory]"
    echo "  Converts all .lisp files in the specified directory (or current directory) to .ipynb"
    echo ""
    echo "Examples:"
    echo "  $0                           # Convert all .lisp files in current directory"
    echo "  $0 experiments/arithmetic    # Convert all .lisp files in experiments/arithmetic"
    exit 1
}

# Get the directory to process
DIR="${1:-.}"

# Check if directory exists
if [ ! -d "$DIR" ]; then
    echo "Error: Directory '$DIR' does not exist"
    exit 1
fi

# Find and convert all .lisp files
LISP_FILES=($(find "$DIR" -maxdepth 1 -name "*.lisp" -type f))

if [ ${#LISP_FILES[@]} -eq 0 ]; then
    echo "No .lisp files found in $DIR"
    exit 0
fi

echo "Found ${#LISP_FILES[@]} .lisp file(s) in $DIR"
echo ""

# Convert each file
for file in "${LISP_FILES[@]}"; do
    python3 "$CONVERTER" "$file"
done

echo ""
echo "Done!"
