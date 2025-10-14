# Lisp to Jupyter Notebook Converter

Scripts to convert ACL2 `.lisp` files into Jupyter `.ipynb` notebooks.

## Usage

### Convert a single file

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

### Convert multiple files

```bash
python3 utils/lisp_to_ipynb.py file1.lisp file2.lisp file3.lisp
```

### Convert all .lisp files in a directory

```bash
./utils/convert_all_lisp.sh [directory]
```

Examples:
```bash
# Convert all .lisp files in current directory
./utils/convert_all_lisp.sh

# Convert all .lisp files in a specific directory
./utils/convert_all_lisp.sh experiments/arithmetic
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
