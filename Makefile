# Minimal makefile for Sphinx documentation
#

# You can set these variables from the command line.
SPHINXOPTS    =
SPHINXBUILD   = python -msphinx
SPHINXPROJ    = programming_in_lean
SOURCEDIR     = .
BUILDDIR      = _build

# Put it first so that "make" without argument is like "make help".
help:
	@$(SPHINXBUILD) -M help "$(SOURCEDIR)" "$(BUILDDIR)" $(SPHINXOPTS) $(O)

VENVDIR := .venv
export PATH := $(VENVDIR)/bin:$(PATH)

install-env:
	test -f $(VENVDIR)/bin/pip || python3 -m venv $(VENVDIR)
	pip install https://bitbucket.org/gebner/pygments-main/get/default.tar.gz#egg=Pygments
	pip install 'wheel>=0.29' # needed for old ubuntu versions, https://github.com/pallets/markupsafe/issues/59

install-deps: install-env
	pip install sphinx

install-travis-deps: install-env
	pip install travis-sphinx

.PHONY: help Makefile

# Catch-all target: route all unknown targets to Sphinx using the new
# "make mode" option.  $(O) is meant as a shortcut for $(SPHINXOPTS).
%: Makefile
	@$(SPHINXBUILD) -M $@ "$(SOURCEDIR)" "$(BUILDDIR)" $(SPHINXOPTS) $(O)
