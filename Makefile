export OCAMLMAKEFILE = ./OCamlMakefile

export LIBS=unix

define PROJ_client
	RESULT =reversi-me
	SOURCES=color.ml command.ml commandParser.mly commandLexer.mll myplay.ml mymain.ml
endef
export PROJ_client

ifndef SUBPROJS
  export SUBPROJS = client
endif

all: byte-code

%:
	@$(MAKE) -f $(OCAMLMAKEFILE) subprojs SUBTARGET=$@
