# Makefile for converting ACL2 .lisp files to Jupyter .ipynb notebooks
# Only rebuilds notebooks when the source .lisp file is newer

# Path to the converter script
CONVERTER := utils/lisp_to_ipynb.py

# Find all .lisp files in experiments directory (excluding .ipynb_checkpoints)
LISP_FILES := $(shell find experiments -name "*.lisp" -type f ! -path "*/.ipynb_checkpoints/*")

# Generate corresponding .ipynb targets
NOTEBOOKS := $(LISP_FILES:.lisp=.ipynb)

# Default target: build all notebooks
.PHONY: all
all: $(NOTEBOOKS)

# Pattern rule: how to build a .ipynb from a .lisp
%.ipynb: %.lisp $(CONVERTER)
	@echo "Converting $< -> $@"
	@python3 $(CONVERTER) $<

# Clean target: remove all generated notebooks
.PHONY: clean
clean:
	@echo "Removing all generated .ipynb files..."
	@rm -f $(NOTEBOOKS)
	@echo "Done!"

# List target: show all .lisp files and their notebook status
.PHONY: list
list:
	@echo "Lisp source files and their notebooks:"
	@for lisp in $(LISP_FILES); do \
		ipynb=$${lisp%.lisp}.ipynb; \
		if [ -f $$ipynb ]; then \
			if [ $$lisp -nt $$ipynb ]; then \
				echo "  [OUT-OF-DATE] $$lisp -> $$ipynb"; \
			else \
				echo "  [UP-TO-DATE]  $$lisp -> $$ipynb"; \
			fi; \
		else \
			echo "  [MISSING]     $$lisp -> $$ipynb"; \
		fi; \
	done

# Check target: list only out-of-date or missing notebooks
.PHONY: check
check:
	@echo "Out-of-date or missing notebooks:"
	@found=0; \
	for lisp in $(LISP_FILES); do \
		ipynb=$${lisp%.lisp}.ipynb; \
		if [ ! -f $$ipynb ]; then \
			echo "  [MISSING]     $$lisp"; \
			found=1; \
		elif [ $$lisp -nt $$ipynb ]; then \
			echo "  [OUT-OF-DATE] $$lisp"; \
			found=1; \
		fi; \
	done; \
	if [ $$found -eq 0 ]; then \
		echo "  All notebooks are up-to-date!"; \
	fi

# Help target
.PHONY: help
help:
	@echo "Makefile for ACL2 .lisp to .ipynb conversion"
	@echo ""
	@echo "Targets:"
	@echo "  make all     - Convert all out-of-date .lisp files to .ipynb (default)"
	@echo "  make clean   - Remove all generated .ipynb files"
	@echo "  make list    - Show all .lisp files and their notebook status"
	@echo "  make check   - Show only out-of-date or missing notebooks"
	@echo "  make help    - Show this help message"
	@echo ""
	@echo "Examples:"
	@echo "  make                              # Build all out-of-date notebooks"
	@echo "  make experiments/lists/experiment-01-list-basics.ipynb"
	@echo "                                    # Build a specific notebook"
	@echo "  make check                        # Check which notebooks need updating"
	@echo ""
	@echo "The converter only rebuilds notebooks when:"
	@echo "  - The .ipynb file doesn't exist, OR"
	@echo "  - The .lisp file is newer than the .ipynb file"
