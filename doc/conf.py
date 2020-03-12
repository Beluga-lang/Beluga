# Configuration file for the Sphinx documentation builder.
#
# This file only contains a selection of the most common options. For a full
# list see the documentation:
# https://www.sphinx-doc.org/en/master/usage/configuration.html

# -- Path setup --------------------------------------------------------------

# If extensions (or modules to document with autodoc) are in another directory,
# add these directories to sys.path here. If the directory is relative to the
# documentation root, use os.path.abspath to make it absolute, like shown here.
#
# import os
# import sys
# sys.path.insert(0, os.path.abspath('.'))


# -- Project information -----------------------------------------------------

project = 'Beluga'
copyright = '2020, Brigitte Pientka, Jacob Errington, Joshua Dunfield, Andrew Cave'
author = 'Brigitte Pientka, Jacob Errington, Joshua Dunfield, Andrew Cave'


# -- General configuration ---------------------------------------------------

# Add any Sphinx extension module names here, as strings. They can be
# extensions coming with Sphinx (named 'sphinx.ext.*') or your custom
# ones.
extensions = [
]

# Add any paths that contain templates here, relative to this directory.
templates_path = ['_templates']

# List of patterns, relative to source directory, that match files and
# directories to ignore when looking for source files.
# This pattern also affects html_static_path and html_extra_path.
exclude_patterns = ['_build', 'Thumbs.db', '.DS_Store']


# -- Options for HTML output -------------------------------------------------

# The theme to use for HTML and HTML Help pages.  See the documentation for
# a list of builtin themes.
#
html_theme = 'alabaster'
html_theme_options = {
    'body_max_width': '100%'
}

# Add any paths that contain custom static files (such as style sheets) here,
# relative to this directory. They are copied after the builtin static files,
# so a file named "default.css" will overwrite the builtin "default.css".
html_static_path = ['_static']

master_doc = 'index'

# Set up Beluga syntax highlighting for documentation.

from pygments.lexer import RegexLexer
from pygments import token

# ['Comment', 'Error', 'Escape', 'Generic', 'Keyword', 'Literal',
# 'Name', 'Number', 'Operator', 'Other', 'Punctuation',
# 'STANDARD_TYPES', 'String', 'Text', 'Token', 'Whitespace',
# '_TokenType', '__builtins__', '__cached__', '__doc__', '__file__',
# '__loader__', '__name__', '__package__', '__spec__',
# 'is_token_subtype', 'string_to_tokentype']

keywords = [
    ( kw + '[^a-zA-Z0-9]', token.Keyword )
    for kw in
    [ 'LF',
      'and',
      'block',
      'case',
      'fn',
      'else',
      'if',
      'impossible',
      'in',
      'let',
      'mlam' ,
      'of',
      'rec',
      'schema',
      'some',
      'then',
      'module',
      'struct',
      'end',
      'trust',
      'total',
      'type',
      'ctype',
      'prop',
      'inductive',
      'coinductive',
      'stratified',
      'LF',
      'fun',
      'typedef',
      'proof',
      'by',
      'as',
      'suffices',
      'toshow',
    ]
]

symbols = [
    ( x, token.Operator )
    for x in
    [ r'\[',
      r'\]',
      r'{',
      r'}',
      r'\(',
      r'\)',
      r'<',
      r'>',
      r'\^',
      r',',
      r'::',
      r':',
      r';',
      r'\|-',
      r'\|',
      r'\\',
      r'\*',
      r'=',
      r'/',
      r'\+',
      r'->',
      r'=>',
      r'\.',
    ]
]

class BelugaLexer (RegexLexer):
    name = 'Beluga'

    tokens = {
        'root':
        keywords +
        symbols +
        [ (r'%.*?$', token.Comment),
          (r'(#\$)?[a-zA-Z_]([a-zA-Z0-9_\'-\*\+@=\^/#\?])*', token.Name),
          (r'\s+', token.Whitespace),
        ]
    }

from sphinx.highlighting import lexers

lexers['Beluga'] = BelugaLexer()
