# Lisp to Jupyter Notebook Converter

Scripts to convert ACL2 `.lisp` files into Jupyter `.ipynb` notebooks.

## Usage

### Using Make (Recommended)

The easiest way to keep notebooks up-to-date is using the Makefile in the project root:

```bash
# Convert all out-of-date notebooks
make

# Check which notebooks need updating
make check

# Show status of all notebooks
make list

# Build a specific notebook
make experiments/lists/experiment-02-higher-order.ipynb

# See all available targets
make help
```

The Makefile automatically:
- Only rebuilds notebooks when the `.lisp` file is newer than the `.ipynb` file
- Tracks dependencies on the converter script
- Skips files in `.ipynb_checkpoints/` directories

### Direct Python Script Usage

For more control, you can use the Python script directly:

#### Convert a single file

```bash
python3 utils/lisp_to_ipynb.py <input.lisp> [output.ipynb]
```

Examples:
```bash
# Convert to default output name (same as input but .ipynb)
python3 utils/lisp_to_ipynb.py experiments/lists/experiment-02-higher-order.lisp

# Specify custom output name
python3 utils/lisp_to_ipynb.py input.lisp custom-output.ipynb
```

#### Convert multiple files

```bash
python3 utils/lisp_to_ipynb.py file1.lisp file2.lisp file3.lisp
```

## Conversion Rules

1. **Cell grouping**: Consecutive non-blank lines are grouped into a single cell
2. **Blank lines**: Act as cell separators
3. **Comment-only blocks**: If all non-blank lines in a group start with `;`, the cell is marked as `raw` (for documentation)
4. **Code blocks**: Any group containing at least one non-comment line is marked as `acl2` code
5. **Language**: All code cells use the `acl2` language identifier

## Example

Input `.lisp` file:
```lisp
; This is a comment block
; It will become a raw cell

(in-package "ACL2")

; This function has a comment but also code
(defun my-func (x)
  (+ x 1))
```

Output `.ipynb` structure:
- Cell 1 (raw): The comment block
- Cell 2 (acl2): `(in-package "ACL2")`
- Cell 3 (acl2): The function definition with its comment

## Requirements

- Python 3.6+
- Standard library only (no external dependencies)

## Files

- `lisp_to_ipynb.py` - Main conversion script
- `convert_all_lisp.sh` - Batch conversion helper script
- `README_CONVERTER.md` - This file
