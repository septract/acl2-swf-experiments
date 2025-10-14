#!/usr/bin/env python3
"""
Convert ACL2 .lisp files to .ipynb notebooks.

Each run of non-blank lines is put into a cell.
Lines that are all comments are marked as 'raw' instead of 'acl2' (code).
"""

import json
import sys
import re
from pathlib import Path
from typing import List, Tuple


def is_comment_line(line: str) -> bool:
    """Check if a line is a comment (starts with ; after whitespace)."""
    stripped = line.lstrip()
    return stripped.startswith(';')


def is_blank_line(line: str) -> bool:
    """Check if a line is blank or only whitespace."""
    return line.strip() == ''


def is_all_comments(lines: List[str]) -> bool:
    """Check if all non-blank lines in a group are comments."""
    non_blank = [line for line in lines if not is_blank_line(line)]
    if not non_blank:
        return False
    return all(is_comment_line(line) for line in non_blank)


def group_lines(lines: List[str]) -> List[Tuple[List[str], str]]:
    """
    Group consecutive non-blank lines into cells.
    Returns list of (lines, cell_type) tuples.
    cell_type is either 'raw' (all comments) or 'acl2' (code).
    """
    groups = []
    current_group = []
    
    for line in lines:
        if is_blank_line(line):
            # End current group if it exists
            if current_group:
                cell_type = 'raw' if is_all_comments(current_group) else 'acl2'
                groups.append((current_group, cell_type))
                current_group = []
        else:
            # Add to current group
            current_group.append(line)
    
    # Don't forget the last group
    if current_group:
        cell_type = 'raw' if is_all_comments(current_group) else 'acl2'
        groups.append((current_group, cell_type))
    
    return groups


def create_notebook_cell(content: str, cell_type: str) -> dict:
    """
    Create a Jupyter notebook cell dictionary.
    cell_type should be 'raw' or 'acl2' (for code cells).
    """
    # Split into lines and add newline to all but the last line
    # This preserves the exact formatting in Jupyter notebooks
    lines = content.split('\n')
    source = [line + '\n' for line in lines[:-1]]
    if lines[-1]:  # Add last line without newline if it's not empty
        source.append(lines[-1])
    
    if cell_type == 'raw':
        return {
            "cell_type": "raw",
            "metadata": {},
            "source": source
        }
    else:
        # ACL2 code cell
        return {
            "cell_type": "code",
            "execution_count": None,
            "metadata": {},
            "outputs": [],
            "source": source
        }


def convert_lisp_to_ipynb(lisp_file: Path, output_file: Path = None):
    """Convert a .lisp file to a .ipynb notebook."""
    if output_file is None:
        output_file = lisp_file.with_suffix('.ipynb')
    
    # Read the lisp file
    with open(lisp_file, 'r', encoding='utf-8') as f:
        lines = f.readlines()
    
    # Strip newlines but keep them for later
    lines = [line.rstrip('\n\r') for line in lines]
    
    # Group lines into cells
    groups = group_lines(lines)
    
    # Create notebook cells
    cells = []
    for line_group, cell_type in groups:
        content = '\n'.join(line_group)
        cell = create_notebook_cell(content, cell_type)
        cells.append(cell)
    
    # Create the notebook structure
    notebook = {
        "cells": cells,
        "metadata": {
            "kernelspec": {
                "display_name": "ACL2",
                "language": "acl2",
                "name": "acl2"
            },
            "language_info": {
                "name": "acl2",
                "version": ""
            }
        },
        "nbformat": 4,
        "nbformat_minor": 2
    }
    
    # Write the notebook
    with open(output_file, 'w', encoding='utf-8') as f:
        json.dump(notebook, f, indent=1, ensure_ascii=False)
        f.write('\n')  # Add trailing newline
    
    print(f"Converted {lisp_file} -> {output_file}")
    print(f"  Created {len(cells)} cells")


def main():
    """Main entry point for the script."""
    if len(sys.argv) < 2:
        print("Usage: lisp_to_ipynb.py <file.lisp> [output.ipynb]")
        print("   or: lisp_to_ipynb.py <file1.lisp> <file2.lisp> ...")
        sys.exit(1)
    
    # Convert each file
    for i, arg in enumerate(sys.argv[1:]):
        lisp_file = Path(arg)
        
        if not lisp_file.exists():
            print(f"Error: File not found: {lisp_file}", file=sys.stderr)
            continue
        
        if not lisp_file.suffix == '.lisp':
            print(f"Warning: {lisp_file} doesn't have .lisp extension, skipping")
            continue
        
        try:
            convert_lisp_to_ipynb(lisp_file)
        except Exception as e:
            print(f"Error converting {lisp_file}: {e}", file=sys.stderr)


if __name__ == '__main__':
    main()
