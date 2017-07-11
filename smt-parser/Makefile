

CUP = java_cup.Main
CUPFLAGS = -nopositions -expect 100

JLEX = JLex.Main

LATEX = latex
DVIPS = dvips
DVIPDF = dvipdfm


PARSER_BASEDIR=$(shell pwd)
PARSER_BINDIR=$(PARSER_BASEDIR)/bin


CLASSPATH:=$(CLASSPATH):$(PARSER_BASEDIR):$(JLEX_PATH)


all: smt-parser.jar ap/parser/smtlib/Test.class


smt-parser.jar: $(PARSER_BINDIR) $(PARSER_BINDIR)/ap/parser/smtlib/Absyn/smtlib.class $(PARSER_BINDIR)/ap/parser/smtlib/sym.class $(PARSER_BINDIR)/ap/parser/smtlib/Yylex.class $(PARSER_BINDIR)/ap/parser/smtlib/PrettyPrinterNonStatic.class $(PARSER_BINDIR)/ap/parser/smtlib/parser.class
	cd $(PARSER_BINDIR) && jar cf $(PARSER_BASEDIR)/smt-parser.jar ap/parser/smtlib


$(PARSER_BINDIR):
	mkdir $(PARSER_BINDIR)

clean:
#	rm -rf parser.jar
	rm -rf $(PARSER_BINDIR)
	rm -rf ap
	rm -rf smtlib.tex smtlib.dvi smtlib.aux smtlib.log smtlib.ps


# just any of the files that is created by bnfc
smtlib.tex: smtlib.cf
	bnfc -java1.5 -p ap.parser smtlib.cf

$(PARSER_BINDIR)/ap/parser/smtlib/Absyn/smtlib.java: smtlib.cf
	bnfc -java1.5 -p ap.parser smtlib.cf
	cd ap/parser/smtlib && patch -p0 <../../../smtlib.cup.patch

$(PARSER_BINDIR)/ap/parser/smtlib/Absyn/smtlib.class: $(PARSER_BINDIR)/ap/parser/smtlib/Absyn/smtlib.java
	${JAVAC} ${JAVAC_FLAGS} -d $(PARSER_BINDIR) ap/parser/smtlib/Absyn/*.java

ap/parser/smtlib/Yylex.java: ap/parser/smtlib/Yylex
#       remove some quotes that JLex does not accept
	sed 's/\\\^/\^/g' <ap/parser/smtlib/Yylex >ap/parser/smtlib/Yylex.temp
	mv ap/parser/smtlib/Yylex.temp ap/parser/smtlib/Yylex
#       quote dashes "-"
	sed 's/\\\+-/\\+\\-/g' <ap/parser/smtlib/Yylex >ap/parser/smtlib/Yylex.temp
	mv ap/parser/smtlib/Yylex.temp ap/parser/smtlib/Yylex
	${JAVA} ${JAVA_FLAGS} ${JLEX} ap/parser/smtlib/Yylex

ap/parser/smtlib/sym.java ap/parser/smtlib/parser.java: ap/parser/smtlib/smtlib.cup
	${JAVA} ${JAVA_FLAGS} ${CUP} ${CUPFLAGS} ap/parser/smtlib/smtlib.cup
	mv sym.java parser.java ap/parser/smtlib/

$(PARSER_BINDIR)/ap/parser/smtlib/Yylex.class: ap/parser/smtlib/Yylex.java ap/parser/smtlib/sym.java
	${JAVAC} ${JAVAC_FLAGS} -d $(PARSER_BINDIR) ap/parser/smtlib/Yylex.java

$(PARSER_BINDIR)/ap/parser/smtlib/sym.class: ap/parser/smtlib/sym.java
	${JAVAC} ${JAVAC_FLAGS} -d $(PARSER_BINDIR) ap/parser/smtlib/sym.java

$(PARSER_BINDIR)/ap/parser/smtlib/parser.class: ap/parser/smtlib/parser.java ap/parser/smtlib/sym.java
	${JAVAC} ${JAVAC_FLAGS} -d $(PARSER_BINDIR) ap/parser/smtlib/parser.java

ap/parser/smtlib/PrettyPrinterNonStatic.java: ap/parser/smtlib/PrettyPrinter.java
	sed 's/PrettyPrinter/PrettyPrinterNonStatic/g' <ap/parser/smtlib/PrettyPrinter.java | sed 's/static//g' >ap/parser/smtlib/PrettyPrinterNonStatic.java

$(PARSER_BINDIR)/ap/parser/smtlib/PrettyPrinter.class: ap/parser/smtlib/PrettyPrinter.java
	${JAVAC} ${JAVAC_FLAGS} -d $(PARSER_BINDIR) ap/parser/smtlib/PrettyPrinter.java

$(PARSER_BINDIR)/ap/parser/smtlib/PrettyPrinterNonStatic.class: ap/parser/smtlib/PrettyPrinterNonStatic.java
	${JAVAC} ${JAVAC_FLAGS} -d $(PARSER_BINDIR) ap/parser/smtlib/PrettyPrinterNonStatic.java

ap/parser/smtlib/Test.class: ap/parser/smtlib/Test.java $(PARSER_BINDIR)/ap/parser/smtlib/PrettyPrinter.class $(PARSER_BINDIR)/ap/parser/smtlib/Yylex.class $(PARSER_BINDIR)/ap/parser/smtlib/parser.class $(PARSER_BINDIR)/ap/parser/smtlib/sym.class
	${JAVAC} ${JAVAC_FLAGS} ap/parser/smtlib/Test.java

smtlib.dvi: smtlib.tex
	${LATEX} smtlib.tex

smtlib.pdf: smtlib.dvi
	${DVIPDF} smtlib.dvi

smtlib.ps: smtlib.dvi
	${DVIPS} smtlib.dvi -o smtlib.ps
