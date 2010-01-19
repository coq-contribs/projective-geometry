##########################################################################
##  v      #                  The Coq Proof Assistant                   ##
## <O___,, # CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud ##
##   \VV/  #                                                            ##
##    //   #   Makefile automagically generated by coq_makefile V8.2    ##
##########################################################################

# WARNING
#
# This Makefile has been automagically generated
# Edit at your own risks !
#
# END OF WARNING

#
# This Makefile was generated by the command line :
# coq_makefile -f Make -o Makefile 
#

# 
# This Makefile may take 3 arguments passed as environment variables:
#   - COQBIN to specify the directory where Coq binaries resides;
#   - CAMLBIN and CAMLP4BIN to give the path for the OCaml and Camlp4/5 binaries.
COQLIB:=$(shell $(COQBIN)coqtop -where | sed -e 's/\\/\\\\/g')
CAMLP4:="$(shell $(COQBIN)coqtop -config | awk -F = '/CAMLP4=/{print $$2}')"
ifndef CAMLP4BIN
  CAMLP4BIN:=$(CAMLBIN)
endif

CAMLP4LIB:=$(shell $(CAMLP4BIN)$(CAMLP4) -where)

##########################
#                        #
# Libraries definitions. #
#                        #
##########################

OCAMLLIBS:=-I Plane/gb\
  -I Plane/gb/ocaml/xml-light
COQSRCLIBS:=-I $(COQLIB)/kernel -I $(COQLIB)/lib \
  -I $(COQLIB)/library -I $(COQLIB)/parsing \
  -I $(COQLIB)/pretyping -I $(COQLIB)/interp \
  -I $(COQLIB)/proofs -I $(COQLIB)/tactics \
  -I $(COQLIB)/toplevel -I $(COQLIB)/contrib/cc -I $(COQLIB)/contrib/dp \
  -I $(COQLIB)/contrib/extraction -I $(COQLIB)/contrib/field \
  -I $(COQLIB)/contrib/firstorder -I $(COQLIB)/contrib/fourier \
  -I $(COQLIB)/contrib/funind -I $(COQLIB)/contrib/interface \
  -I $(COQLIB)/contrib/micromega -I $(COQLIB)/contrib/omega \
  -I $(COQLIB)/contrib/ring -I $(COQLIB)/contrib/romega \
  -I $(COQLIB)/contrib/rtauto -I $(COQLIB)/contrib/setoid_ring \
  -I $(COQLIB)/contrib/subtac -I $(COQLIB)/contrib/xml
COQLIBS:= -R . ProjectiveGeometry
COQDOCLIBS:=-R . ProjectiveGeometry

##########################
#                        #
# Variables definitions. #
#                        #
##########################

ZFLAGS=$(OCAMLLIBS) $(COQSRCLIBS) -I $(CAMLP4LIB)
OPT:=
COQFLAGS:=-q $(OPT) $(COQLIBS) $(OTHERFLAGS) $(COQ_XML)
ifdef CAMLBIN
  COQMKTOPFLAGS:=-camlbin $(CAMLBIN) -camlp4bin $(CAMLP4BIN)
endif
COQC:=$(COQBIN)coqc
COQDEP:=$(COQBIN)coqdep -c
GALLINA:=$(COQBIN)gallina
COQDOC:=$(COQBIN)coqdoc
COQMKTOP:=$(COQBIN)coqmktop
CAMLC:=$(CAMLBIN)ocamlc.opt -c -rectypes
CAMLOPTC:=$(CAMLBIN)ocamlopt.opt -c -rectypes
CAMLLINK:=$(CAMLBIN)ocamlc.opt -rectypes
CAMLOPTLINK:=$(CAMLBIN)ocamlopt.opt -rectypes
GRAMMARS:=grammar.cma
CAMLP4EXTEND:=pa_extend.cmo pa_macro.cmo q_MLast.cmo
CAMLP4OPTIONS:=
PP:=-pp "$(CAMLP4BIN)$(CAMLP4)o -I . $(COQSRCLIBS) $(CAMLP4EXTEND) $(GRAMMARS) $(CAMLP4OPTIONS) -impl"

###################################
#                                 #
# Definition of the "all" target. #
#                                 #
###################################

VFILES:=Plane/back.v\
  Plane/projective_plane_axioms.v\
  Plane/decidability.v\
  Plane/field_variable_isolation_tactic.v\
  Plane/flat.v\
  Plane/pg25.v\
  Plane/gb/gbtypes.v\
  Plane/gb/gb.v\
  Plane/general_tactics.v\
  Plane/forth.v\
  Plane/basic_facts_plane.v\
  Plane/projective_plane_inst.v\
  Plane/homogeneous.v\
  Plane/bij.v\
  Plane/examples.v\
  Plane/P05_almost_pappus.v\
  Plane/P06_angle_line.v\
  Plane/P07_cevian_lines.v\
  Plane/P08_cevian_lines_2.v\
  Plane/P09_complete_quadrilateral.v\
  Plane/P10_complete_quadrilateral_2.v\
  Plane/P11_chasles.v\
  Plane/P12_aeolian.v\
  Plane/P14_pseudo_midpoint.v\
  Plane/hexamys.v\
  Plane/fano_plane.v\
  Plane/fano_plane_desargues.v\
  Plane/Heyting_projective_plane_axioms.v\
  Plane/projective_plane_to_Heyting_projective_plane.v\
  Plane/projective_plane_duality.v\
  Plane/gb/gbtypes.v\
  Space/desargues3Dlemmas.v\
  Space/matroids_axioms.v\
  Space/matroid_to_matroid_p.v\
  Space/desargues2Dlemmas.v\
  Space/projective_space_rank_axioms.v\
  Space/sets_of_points.v\
  Space/rank_properties.v\
  Space/desargues2Dlemmas3.v\
  Space/desargues3Dspecial.v\
  Space/field_variable_isolation_tactic.v\
  Space/projective_space_rank_to_projective_space.v\
  Space/desargues2Dmore.v\
  Space/general_tactics.v\
  Space/desarguesxD.v\
  Space/basic_facts.v\
  Space/matroids_properties.v\
  Space/desargues2D.v\
  Space/desargues3D.v\
  Space/projective_space_axioms.v\
  Space/desargues2Dlemmas2.v
VOFILES:=$(VFILES:.v=.vo)
GLOBFILES:=$(VFILES:.v=.glob)
VIFILES:=$(VFILES:.v=.vi)
GFILES:=$(VFILES:.v=.g)
HTMLFILES:=$(VFILES:.v=.html)
GHTMLFILES:=$(VFILES:.v=.g.html)
MLFILES:=Plane/gb/entiers.ml\
  Plane/gb/utile.ml\
  Plane/gb/polynomes2.ml\
  Plane/gb/dansideal.ml
CMOFILES:=$(MLFILES:.ml=.cmo)
CMIFILES:=$(MLFILES:.ml=.cmi)
CMXFILES:=$(MLFILES:.ml=.cmx)
CMXSFILES:=$(MLFILES:.ml=.cmxs)
OFILES:=$(MLFILES:.ml=.o)

all: $(VOFILES) $(CMOFILES) $(CMXSFILES) Plane/gb/ocaml/xml-light/xml-light.cma\
  Plane/gb/gb\
  Plane/gb/gb.vo Plane/gb/gb.glob
spec: $(VIFILES)

gallina: $(GFILES)

html: $(GLOBFILES) $(VFILES)
	- mkdir html
	$(COQDOC) -toc -html $(COQDOCLIBS) -d html $(VFILES)

gallinahtml: $(GLOBFILES) $(VFILES)
	- mkdir html
	$(COQDOC) -toc -html -g $(COQDOCLIBS) -d html $(VFILES)

all.ps: $(VFILES)
	$(COQDOC) -toc -ps $(COQDOCLIBS) -o $@ `$(COQDEP) -sort -suffix .v $(VFILES)`

all-gal.ps: $(VFILES)
	$(COQDOC) -toc -ps -g $(COQDOCLIBS) -o $@ `$(COQDEP) -sort -suffix .v $(VFILES)`

all.pdf: $(VFILES)
	$(COQDOC) -toc -pdf $(COQDOCLIBS) -o $@ `$(COQDEP) -sort -suffix .v $(VFILES)`

all-gal.pdf: $(VFILES)
	$(COQDOC) -toc -pdf -g $(COQDOCLIBS) -o $@ `$(COQDEP) -sort -suffix .v $(VFILES)`



###################
#                 #
# Custom targets. #
#                 #
###################

Plane/gb/ocaml/xml-light/xml-light.cma: 
	cd Plane/gb/ocaml/xml-light; make all; cd ../../..

Plane/gb/gb: Plane/gb/entiers.cmo Plane/gb/polynomes2.cmo Plane/gb/utile.cmo Plane/gb/dansideal.cmo Plane/gb/ocaml/xml-light/xml-light.cma
	$(CAMLBIN)ocamlc -rectypes $(ZDEBUG) $(ZFLAGS) -o Plane/gb/gb unix.cma nums.cma xml-light.cma  Plane/gb/utile.cmo Plane/gb/entiers.cmo Plane/gb/polynomes2.cmo Plane/gb/dansideal.cmo Plane/gb/gb.ml

Plane/gb/gb.vo Plane/gb/gb.glob: Plane/gb/gb.v Plane/gb/gbtypes.vo Plane/gb/gb
	$(COQC) -dump-glob Plane/gb/gb.glob $(COQDEBUG) $(COQFLAGS) $<

####################
#                  #
# Special targets. #
#                  #
####################

.PHONY: all opt byte archclean clean install depend html

%.cmi: %.mli
	$(CAMLC) $(ZDEBUG) $(ZFLAGS) $<

%.cmo: %.ml
	$(CAMLC) $(ZDEBUG) $(ZFLAGS) $(PP) $<

%.cmx: %.ml
	$(CAMLOPTC) $(ZDEBUG) $(ZFLAGS) $(PP) $<

%.cmxs: %.ml
	$(CAMLOPTLINK) $(ZDEBUG) $(ZFLAGS) -shared -o $@ $(PP) $<

%.cmo: %.ml4
	$(CAMLC) $(ZDEBUG) $(ZFLAGS) $(PP) -impl $<

%.cmx: %.ml4
	$(CAMLOPTC) $(ZDEBUG) $(ZFLAGS) $(PP) -impl $<

%.cmxs: %.ml4
	$(CAMLOPTLINK) $(ZDEBUG) $(ZFLAGS) -shared -o $@ $(PP) -impl $<

%.ml.d: %.ml
	$(CAMLBIN)ocamldep -slash $(COQSRCLIBS) $(OCAMLLIBS) $(PP) "$<" > "$@"

%.vo %.glob: %.v
	$(COQC) -dump-glob $*.glob $(COQDEBUG) $(COQFLAGS) $*

%.vi: %.v
	$(COQC) -i $(COQDEBUG) $(COQFLAGS) $*

%.g: %.v
	$(GALLINA) $<

%.tex: %.v
	$(COQDOC) -latex $< -o $@

%.html: %.v %.glob
	$(COQDOC) -glob-from $*.glob  -html $< -o $@

%.g.tex: %.v
	$(COQDOC) -latex -g $< -o $@

%.g.html: %.v %.glob
	$(COQDOC) -glob-from $*.glob -html -g $< -o $@

%.v.d: %.v
	$(COQDEP) -glob -slash $(COQLIBS) "$<" > "$@" || ( RV=$$?; rm -f "$@"; exit $${RV} )

byte:
	$(MAKE) all "OPT:=-byte"

opt:
	$(MAKE) all "OPT:=-opt"

install:
	mkdir -p $(COQLIB)/user-contrib
	(for i in $(VOFILES); do \
	 install -D $$i $(COQLIB)/user-contrib/ProjectiveGeometry/$$i; \
	 done)
	(for i in $(CMOFILES); do \
	 install -D $$i $(COQLIB)/user-contrib/ProjectiveGeometry/$$i; \
	 done)
	(for i in $(CMIFILES); do \
	 install -D $$i $(COQLIB)/user-contrib/ProjectiveGeometry/$$i; \
	 done)
	(for i in $(CMXSFILES); do \
	 install -D $$i $(COQLIB)/user-contrib/ProjectiveGeometry/$$i; \
	 done)

clean:
	rm -f $(VOFILES) $(VIFILES) $(GFILES) *~
	rm -f all.ps all-gal.ps all.pdf all-gal.pdf all.glob $(VFILES:.v=.glob) $(HTMLFILES) $(GHTMLFILES) $(VFILES:.v=.tex) $(VFILES:.v=.g.tex) $(VFILES:.v=.v.d)
	rm -f $(CMOFILES) $(MLFILES:.ml=.cmi) $(MLFILES:.ml=.ml.d) $(MLFILES:.ml=.cmx) $(MLFILES:.ml=.o)
	rm -f $(CMXSFILES) $(CMXSFILES:.cmxs=.o)
	- rm -rf html
	- rm -f Plane/gb/ocaml/xml-light/xml-light.cma
	- rm -f Plane/gb/gb
	- rm -f Plane/gb/gb.vo Plane/gb/gb.glob

archclean:
	rm -f *.cmx *.o


printenv: 
	@echo CAMLC =	$(CAMLC)
	@echo CAMLOPTC =	$(CAMLOPTC)
	@echo CAMLP4LIB =	$(CAMLP4LIB)

Makefile: Make
	mv -f Makefile Makefile.bak
	$(COQBIN)coq_makefile -f Make -o Makefile


-include $(VFILES:.v=.v.d)
.SECONDARY: $(VFILES:.v=.v.d)

-include $(MLFILES:.ml=.ml.d)
.SECONDARY: $(MLFILES:.ml=.ml.d)

# WARNING
#
# This Makefile has been automagically generated
# Edit at your own risks !
#
# END OF WARNING

