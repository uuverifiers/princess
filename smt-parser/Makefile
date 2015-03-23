

CUP = java_cup.Main
CUPFLAGS = -nopositions -expect 100

JLEX = JLex.Main

LATEX = latex
DVIPS = dvips
DVIPDF = dvipdfm


PARSER_BASEDIR=$(shell pwd)
PARSER_BINDIR=$(PARSER_BASEDIR)/bin


CLASSPATH:=$(CLASSPATH):$(PARSER_BASEDIR):$(JLEX_PATH)


all: smt-parser.jar smtlib/Test.class


smt-parser.jar: $(PARSER_BINDIR) $(PARSER_BINDIR)/smtlib/Absyn/smtlib.class $(PARSER_BINDIR)/smtlib/sym.class $(PARSER_BINDIR)/smtlib/Yylex.class $(PARSER_BINDIR)/smtlib/PrettyPrinterNonStatic.class $(PARSER_BINDIR)/smtlib/parser.class
	cd $(PARSER_BINDIR) && jar cf $(PARSER_BASEDIR)/smt-parser.jar smtlib


$(PARSER_BINDIR):
	mkdir $(PARSER_BINDIR)

clean:
#	rm -rf parser.jar
	rm -rf $(PARSER_BINDIR)
	rm -rf smtlib
	rm -rf smtlib.tex smtlib.dvi smtlib.aux smtlib.log smtlib.ps


# just any of the files that is created by bnfc
smtlib.tex: smtlib.cf
	bnfc -java1.5 smtlib.cf

$(PARSER_BINDIR)/smtlib/Absyn/smtlib.java: smtlib.cf
	bnfc -java1.5 smtlib.cf
	cd smtlib && patch -p0 <../smtlib.cup.patch

$(PARSER_BINDIR)/smtlib/Absyn/smtlib.class: $(PARSER_BINDIR)/smtlib/Absyn/smtlib.java
	${JAVAC} ${JAVAC_FLAGS} -d $(PARSER_BINDIR) smtlib/Absyn/*.java

smtlib/Yylex.java: smtlib/Yylex
#       remove some quotes that JLex does not accept
	sed 's/\\\^/\^/g' <smtlib/Yylex >smtlib/Yylex.temp
	mv smtlib/Yylex.temp smtlib/Yylex
#       quote dashes "-"
	sed 's/\\\+-/\\+\\-/g' <smtlib/Yylex >smtlib/Yylex.temp
	mv smtlib/Yylex.temp smtlib/Yylex
	${JAVA} ${JAVA_FLAGS} ${JLEX} smtlib/Yylex

smtlib/sym.java smtlib/parser.java: smtlib/smtlib.cup
	${JAVA} ${JAVA_FLAGS} ${CUP} ${CUPFLAGS} smtlib/smtlib.cup
	mv sym.java parser.java smtlib/

$(PARSER_BINDIR)/smtlib/Yylex.class: smtlib/Yylex.java smtlib/sym.java
	${JAVAC} ${JAVAC_FLAGS} -d $(PARSER_BINDIR) smtlib/Yylex.java

$(PARSER_BINDIR)/smtlib/sym.class: smtlib/sym.java
	${JAVAC} ${JAVAC_FLAGS} -d $(PARSER_BINDIR) smtlib/sym.java

$(PARSER_BINDIR)/smtlib/parser.class: smtlib/parser.java smtlib/sym.java
	${JAVAC} ${JAVAC_FLAGS} -d $(PARSER_BINDIR) smtlib/parser.java

smtlib/PrettyPrinterNonStatic.java: smtlib/PrettyPrinter.java
	sed 's/PrettyPrinter/PrettyPrinterNonStatic/g' <smtlib/PrettyPrinter.java | sed 's/static//g' >smtlib/PrettyPrinterNonStatic.java

$(PARSER_BINDIR)/smtlib/PrettyPrinter.class: smtlib/PrettyPrinter.java
	${JAVAC} ${JAVAC_FLAGS} -d $(PARSER_BINDIR) smtlib/PrettyPrinter.java

$(PARSER_BINDIR)/smtlib/PrettyPrinterNonStatic.class: smtlib/PrettyPrinterNonStatic.java
	${JAVAC} ${JAVAC_FLAGS} -d $(PARSER_BINDIR) smtlib/PrettyPrinterNonStatic.java

smtlib/Test.class: smtlib/Test.java $(PARSER_BINDIR)/smtlib/PrettyPrinter.class $(PARSER_BINDIR)/smtlib/Yylex.class $(PARSER_BINDIR)/smtlib/parser.class $(PARSER_BINDIR)/smtlib/sym.class
	${JAVAC} ${JAVAC_FLAGS} smtlib/Test.java

smtlib.dvi: smtlib.tex
	${LATEX} smtlib.tex

smtlib.pdf: smtlib.dvi
	${DVIPDF} smtlib.dvi

smtlib.ps: smtlib.dvi
	${DVIPS} smtlib.dvi -o smtlib.ps
