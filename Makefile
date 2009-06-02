######################################################################
# How to use this Makefile
#
# make		-- build optimized executable in opt/
# make gprof	-- build executable for profiling with gprof in gprof/
# make debug	-- build executable for debugging with gdb in debug/
# make clean	-- clean generated files for optimized version
# make cleanall	-- clean generated files for all above versions, and
#                  dependency files.
######################################################################

#top:	all

go:
	javac -source 1.4 -g guru/*.java guru/compiler/*java

carraway:
	javac -source 1.4 -g guru/*.java guru/carraway/*java

# the name of the C++ compiler
GCJ=gcj

# the default version
VERSION=opt

# set GPP_OPTS according to version
ifeq ($(VERSION),debug)
  GCJ_OPTS = -O0 -ggdb
else
  ifeq ($(VERSION),gprof)
    GCJ_OPTS = -O -pg
  else
    # optimized versions
    GCJ_OPTS = -O
  endif
endif

DIR=./$(VERSION)

SRC=$(wildcard guru/*.java guru/compiler/*.java)
DEP=$(patsubst guru/%.java, deps/%.d, $(SRC))
OBJ=$(patsubst guru/%.java, $(DIR)/%.o, $(SRC))

all: 	Makefile.d
	mkdir -p $(DIR)
	mkdir -p $(DIR)/compiler
	$(MAKE) VERSION=$(VERSION) $(DIR)/guru

Src:
	echo $(SRC)

Opt:	
	$(MAKE) VERSION=opt INC=1 all

Gprof:	
	$(MAKE) VERSION=gprof INC=1 all

Debug:	
	$(MAKE) VERSION=debug INC=1 all

$(DIR)/guru: $(OBJ)
	$(GCJ) $(GCJ_OPTS) --main=guru.Main -o $(DIR)/guru $(OBJ)

$(DIR)/%.o : guru/%.java
	$(GCJ) $(GCJ_OPTS) -c $< -o $@

deps/%.d : guru/%.java
	$(GCJ) -MM -MF $@ -MT $(DIR)/$*.o -c $<

deps/:
	mkdir -p deps
	mkdir -p deps/compiler

Makefile.d: deps/ $(DEP)
	cat $(DEP) > Makefile.d

clean:
	rm -f $(DIR)/guru $(OBJ)

cleanall:
	$(MAKE) clean
	$(MAKE) VERSION=gprof clean
	$(MAKE) VERSION=debug clean
	rm -f Makefile.d $(DEP)

ifdef INC
include Makefile.d
endif

