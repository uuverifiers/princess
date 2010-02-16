

CUP = java_cup.Main
CUPFLAGS = -nopositions -expect 100

JLEX = JLex.Main

LATEX = latex
DVIPS = dvips
DVIPDF = dvipdfm


PARSER_BASEDIR=$(shell pwd)
PARSER_BINDIR=$(PARSER_BASEDIR)/bin


CLASSPATH:=$(CLASSPATH):$(PARSER_BASEDIR):$(JLEX_PATH)


all: parser.jar ApInput/Test.class


parser.jar: $(PARSER_BINDIR) $(PARSER_BINDIR)/ApInput/Absyn/ApInput.class $(PARSER_BINDIR)/ApInput/sym.class $(PARSER_BINDIR)/ApInput/Yylex.class $(PARSER_BINDIR)/ApInput/PrettyPrinter.class $(PARSER_BINDIR)/ApInput/parser.class
	cd $(PARSER_BINDIR) && jar cf $(PARSER_BASEDIR)/parser.jar ApInput


$(PARSER_BINDIR):
	mkdir $(PARSER_BINDIR)

clean:
#	rm -rf parser.jar
	rm -rf $(PARSER_BINDIR)
	rm -rf ApInput
	rm -rf ApInput.tex ApInput.dvi ApInput.aux ApInput.log ApInput.ps


# just any of the files that is created by bnfc
ApInput.tex: ApInput.cf
	bnfc -java1.5 ApInput.cf

$(PARSER_BINDIR)/ApInput/Absyn/ApInput.java: ApInput.cf
	bnfc -java1.5 ApInput.cf

$(PARSER_BINDIR)/ApInput/Absyn/ApInput.class: $(PARSER_BINDIR)/ApInput/Absyn/ApInput.java
	${JAVAC} ${JAVAC_FLAGS} -d $(PARSER_BINDIR) ApInput/Absyn/*.java

ApInput/Yylex.java: ApInput/Yylex
	${JAVA} ${JAVA_FLAGS} ${JLEX} ApInput/Yylex

ApInput/sym.java ApInput/parser.java: ApInput/ApInput.cup
	${JAVA} ${JAVA_FLAGS} ${CUP} ${CUPFLAGS} ApInput/ApInput.cup
	mv sym.java parser.java ApInput/

$(PARSER_BINDIR)/ApInput/Yylex.class: ApInput/Yylex.java ApInput/sym.java
	${JAVAC} ${JAVAC_FLAGS} -d $(PARSER_BINDIR) ApInput/Yylex.java

$(PARSER_BINDIR)/ApInput/sym.class: ApInput/sym.java
	${JAVAC} ${JAVAC_FLAGS} -d $(PARSER_BINDIR) ApInput/sym.java

$(PARSER_BINDIR)/ApInput/parser.class: ApInput/parser.java ApInput/sym.java
	${JAVAC} ${JAVAC_FLAGS} -d $(PARSER_BINDIR) ApInput/parser.java

$(PARSER_BINDIR)/ApInput/PrettyPrinter.class: ApInput/PrettyPrinter.java
	${JAVAC} ${JAVAC_FLAGS} -d $(PARSER_BINDIR) ApInput/PrettyPrinter.java

ApInput/Test.class: ApInput/Test.java $(PARSER_BINDIR)/ApInput/PrettyPrinter.class $(PARSER_BINDIR)/ApInput/Yylex.class $(PARSER_BINDIR)/ApInput/parser.class $(PARSER_BINDIR)/ApInput/sym.class
	${JAVAC} ${JAVAC_FLAGS} ApInput/Test.java

ApInput.dvi: ApInput.tex
	${LATEX} ApInput.tex

ApInput.pdf: ApInput.dvi
	${DVIPDF} ApInput.dvi

ApInput.ps: ApInput.dvi
	${DVIPS} ApInput.dvi -o ApInput.ps
