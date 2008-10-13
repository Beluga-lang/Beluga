# -*- coding: utf-8; indent-tabs-mode: t; -*-

CORE_CFLAGS=-cflags '-w A','-warn-error A'
CORE_CFLAGS_OPT=-cflags -noassert,-unsafe,'-ccopt -O3','-w A','-warn-error A'
CORE_DIR=core
CORE_DOC_NAME=core
CORE_LFLAGS=
CORE_LIBS=
CORE_NAME=core

DOC_CFLAGS=
DOC_LFLAGS=
DOC_LIBS=

FRONT_CFLAGS=-cflags '-w A','-warn-error A'
FRONT_CFLAGS_OPT=-cflags -noassert,-unsafe,'-ccopt -O3'
FRONT_DIR=frontend
FRONT_DOC_NAME=frontend
FRONT_LFLAGS=
FRONT_LIBS=
FRONT_NAME=frontend

INT_CFLAGS=-cflags '-w A','-warn-error A'
INT_CFLAGS_OPT=-cflags -noassert,-unsafe,'-ccopt -O3'
INT_DIR=interpreter
INT_DOC_NAME=interpreter
INT_LFLAGS=
INT_LIBS=-libs extlib
INT_NAME=interpreter

TOP_CFLAGS=-cflags '-w A','-warn-error A'
TOP_CFLAGS_OPT=
TOP_LFLAGS=
TOP_LIBS=
TOP_NAME=beluga

JOBS=-j 0
OCAMLBUILD=ocamlbuild
SCRIPTS_DIR=../scripts



all:	beluga-core beluga-frontend #beluga-interpreter

clean:
	@${OCAMLBUILD} -clean

dist:
	@echo "\nTarget 'dist' not yet implemented."

doc:	beluga-doc

interactive:	all top
	@ledit ./beluga.top -I _build

opt:	beluga-core-opt beluga-frontend-opt beluga-interpreter-opt

prof:
	@echo "\nTarget 'prof' not yet implemented."

top:	beluga-toplevel

world.opt:	opt




beluga-core:
	@echo "\nBuilding Beluga Core..."
	@${OCAMLBUILD} ${JOBS} ${CORE_CFLAGS} ${CORE_LFLAGS} ${CORE_LIBS}\
	 ${CORE_NAME}.cmx

beluga-frontend:
	@echo "\nBuilding Beluga Frontend..."
	@${OCAMLBUILD} ${JOBS} ${FRONT_CFLAGS} ${FRONT_LFLAGS} ${FRONT_LIBS}\
	 ${FRONT_NAME}.cmx

beluga-interpreter:
	@echo "\nBuilding Beluga Interpreter..."
	@${OCAMLBUILD} ${JOBS} ${INT_CFLAGS} ${INT_LFLAGS} ${INT_LIBS} ${INT_NAME}.cmx




beluga-core-opt:
	@echo "\nBuilding Beluga Core... (Optimized)"
	@${OCAMLBUILD} ${JOBS} ${CORE_CFLAGS_OPT} ${CORE_LFLAGS} ${CORE_LIBS}\
	${CORE_NAME}.cmx

beluga-frontend-opt:
	@echo "\nBuilding Beluga Frontend... (Optimized)"
	@${OCAMLBUILD} ${JOBS} ${FRONT_CFLAGS_OPT} ${FRONT_LFLAGS} ${FRONT_LIBS}\
	 ${FRONT_NAME}.cmx

beluga-interpreter-opt:
	@echo "\nGenerating Beluga Interpreter... (Optimized)"
	@${OCAMLBUILD} ${JOBS} ${INT_CFLAGS_OPT} ${INT_LFLAGS} ${INT_LIBS}\
	 ${INT_NAME}.cmx





beluga-doc:
	@echo "\nGenerating Beluga Documentation..."
	@echo "FIXME"
#	@${OCAMLBUILD} ${JOBS} ${DOC_CFLAGS} ${DOC_LFLAGS} ${DOC_LIBS}\
#	 beluga.docdir/index.html
#	 ${CORE_DIR}/${CORE_DOC_NAME}.docdir/index.html\
#	 ${FRONT_DIR}/${FRONT_DOC_NAME}.docdir/index.html
#	 ${INT_DIR}/${INT_DOC_NAME}.docdir/index.html
#	@${SCRIPTS_DIR}/fix-doc-html-charset.sh ${CORE_DOC_NAME}.docdir
#	@${SCRIPTS_DIR}/fix-doc-html-charset.sh ${FRONT_DOC_NAME}.docdir
#	@${SCRIPTS_DIR}/fix-doc-html-charset.sh ${INT_DOC_NAME}.docdir





beluga-toplevel:
	@echo "\nBuilding Customized OCaml toplevel w/ Beluga Support"
	@${OCAMLBUILD} ${JOBS} ${TOP_CFLAGS} ${TOP_LFLAGS} ${TOP_LIBS} ${TOP_NAME}.top
