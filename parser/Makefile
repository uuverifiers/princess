

CUP = java_cup.Main
CUPFLAGS = -locations -expect 100

JFLEX = jflex.Main

LATEX = latex
DVIPS = dvips
DVIPDF = dvipdfm


PARSER_BASEDIR=$(shell pwd)
PARSER_BINDIR=$(PARSER_BASEDIR)/bin


CLASSPATH:=$(CLASSPATH):$(PARSER_BASEDIR):$(JLEX_PATH)


all: parser.jar ap/parser/ap_input/Test.class


parser.jar: $(PARSER_BINDIR) $(PARSER_BINDIR)/ap/parser/ap_input/Absyn/ApInput.class $(PARSER_BINDIR)/ap/parser/ap_input/sym.class $(PARSER_BINDIR)/ap/parser/ap_input/Yylex.class $(PARSER_BINDIR)/ap/parser/ap_input/PrettyPrinter.class $(PARSER_BINDIR)/ap/parser/ap_input/parser.class
	cd $(PARSER_BINDIR) && jar cf $(PARSER_BASEDIR)/parser.jar ap/parser/ap_input


$(PARSER_BINDIR):
	mkdir $(PARSER_BINDIR)

clean:
#	rm -rf parser.jar
	rm -rf $(PARSER_BINDIR)
	rm -rf ap
	rm -rf ApInput.tex ApInput.dvi ApInput.aux ApInput.log ApInput.ps


# just any of the files that is created by bnfc
ApInput.tex: ApInput.cf
	bnfc -p ap.parser ApInput.cf --java --jflex -l

$(PARSER_BINDIR)/ap/parser/ap_input/Absyn/ApInput.java: ApInput.cf
	bnfc -p ap.parser ApInput.cf --java --jflex -l

$(PARSER_BINDIR)/ap/parser/ap_input/Absyn/ApInput.class: $(PARSER_BINDIR)/ap/parser/ap_input/Absyn/ApInput.java
	${JAVAC} ${JAVAC_FLAGS} -d $(PARSER_BINDIR) ap/parser/ap_input/Absyn/*.java

ap/parser/ap_input/Yylex.java: ap/parser/ap_input/Yylex
	${JAVA} ${JAVA_FLAGS} ${JFLEX} ap/parser/ap_input/Yylex

ap/parser/ap_input/sym.java ap/parser/ap_input/parser.java: ap/parser/ap_input/_cup.cup
	${JAVA} ${JAVA_FLAGS} ${CUP} ${CUPFLAGS} ap/parser/ap_input/_cup.cup
	mv sym.java parser.java ap/parser/ap_input/

$(PARSER_BINDIR)/ap/parser/ap_input/Yylex.class: ap/parser/ap_input/Yylex.java ap/parser/ap_input/sym.java
	${JAVAC} ${JAVAC_FLAGS} -d $(PARSER_BINDIR) ap/parser/ap_input/Yylex.java

$(PARSER_BINDIR)/ap/parser/ap_input/sym.class: ap/parser/ap_input/sym.java
	${JAVAC} ${JAVAC_FLAGS} -d $(PARSER_BINDIR) ap/parser/ap_input/sym.java

$(PARSER_BINDIR)/ap/parser/ap_input/parser.class: ap/parser/ap_input/parser.java ap/parser/ap_input/sym.java
	${JAVAC} ${JAVAC_FLAGS} -d $(PARSER_BINDIR) ap/parser/ap_input/parser.java

$(PARSER_BINDIR)/ap/parser/ap_input/PrettyPrinter.class: ap/parser/ap_input/PrettyPrinter.java
	${JAVAC} ${JAVAC_FLAGS} -d $(PARSER_BINDIR) ap/parser/ap_input/PrettyPrinter.java

ap/parser/ap_input/Test.class: ap/parser/ap_input/Test.java $(PARSER_BINDIR)/ap/parser/ap_input/PrettyPrinter.class $(PARSER_BINDIR)/ap/parser/ap_input/Yylex.class $(PARSER_BINDIR)/ap/parser/ap_input/parser.class $(PARSER_BINDIR)/ap/parser/ap_input/sym.class
	${JAVAC} ${JAVAC_FLAGS} ap/parser/ap_input/Test.java

ApInput.dvi: ApInput.tex
	${LATEX} ApInput.tex

ApInput.pdf: ApInput.dvi
	${DVIPDF} ApInput.dvi

ApInput.ps: ApInput.dvi
	${DVIPS} ApInput.dvi -o ApInput.ps
