/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2009-2017 Philipp Ruemmer <ph_r@gmx.net>
 *
 * Princess is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published by
 * the Free Software Foundation, either version 2.1 of the License, or
 * (at your option) any later version.
 *
 * Princess is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with Princess.  If not, see <http://www.gnu.org/licenses/>.
 */

package ap;

import ap.parameters.{GlobalSettings, Param}
import ap.util.CmdlParser

import scala.collection.mutable.ArrayBuffer
import scala.concurrent.{Future, ExecutionContext}
import java.util.concurrent.Executors

import java.io.File
import javax.swing._
import java.awt.{BorderLayout, FlowLayout, Dimension, Font, Color, Point}
import java.awt.event.{ActionEvent, ActionListener, MouseAdapter,
                       MouseEvent, KeyEvent, MouseWheelEvent}
import javax.swing.event.{DocumentListener, DocumentEvent}

object DialogMain {
  
  def main(args : Array[String]) : Unit = {
    val dialog = new InputDialog
    // we assume that given arguments are files to be loaded
    for (s <- args)
      dialog loadFile (new File (s))
  }
  
}

object DialogUtil {
  
  def asString[A](computation : => A) : String =
    captureOutput(computation) _2

  def captureOutput[A](computation : => A) : (A, String) = {
    val buffer = new java.io.ByteArrayOutputStream
    val res = Console.withOut(buffer) (computation)
    (res, buffer.toString)
  }

  def doLater[A](computation : => A) =
    SwingUtilities.invokeLater(new Runnable {
      def run = computation
    })
  
  def ss(c : java.awt.Component,
         minWidth : Int, prefWidth : Int,
         minHeight : Int, prefHeight : Int) = {
    c.setMinimumSize(new Dimension(minWidth, minHeight))
    c.setPreferredSize(new Dimension(prefWidth, prefHeight))
  }
  
  def vScrolled(c : JComponent) =
    new JScrollPane(c,
                    javax.swing.ScrollPaneConstants.VERTICAL_SCROLLBAR_ALWAYS,
                    javax.swing.ScrollPaneConstants.HORIZONTAL_SCROLLBAR_AS_NEEDED)

  def setupTextField(f : JTextArea) =
    f.setFont(new Font("Courier", Font.PLAIN, 14)) 

  def addActionListener(x : AbstractButton)(action : => Unit) =
    x addActionListener (new ActionListener {
      def actionPerformed(e : ActionEvent) = action
    })

  def updateTextField(outputField : JTextArea, stream : java.io.InputStream)
                     (implicit ec : ExecutionContext) =
    Future {
      val buf = new StringBuffer
      var c = stream.read
      while (c != -1) {
        buf append c.toChar
        if (stream.available == 0) {
          // otherwise, read all available data and
          // display it at once
          val str = buf.toString
          buf.delete(0, buf.length)
          doLater {
            outputField append str
          }
        }
        c = stream.read
      }
    }

  class MouseWheelZoomer(field : JTextArea) extends MouseAdapter {
    var currentSize : Double = field.getFont.getSize
    override def mouseWheelMoved(e : MouseWheelEvent) =
      if (e.isControlDown) {
        currentSize =
          if (currentSize <= 15)
            ((currentSize - e.getWheelRotation) max 5).toInt
          else
            currentSize * (20.0 - e.getWheelRotation) / 20.0

        val oldFont = field.getFont
        val newFont = new Font (oldFont.getName, oldFont.getStyle, currentSize.toInt)
        field setFont newFont
      } else {
        e.getComponent.getParent.dispatchEvent(e)
      }
  }

}

////////////////////////////////////////////////////////////////////////////////

class InputDialog extends JPanel {

  import DialogUtil._

  private implicit val ec =
    ExecutionContext fromExecutor Executors.newCachedThreadPool
  
  //////////////////////////////////////////////////////////////////////////////

  private val frame = new JFrame ("Princess")
  frame add this
  ss(frame, 400, 800, 400, 800)
  
  setLayout(new BorderLayout)
  frame.setDefaultCloseOperation(JFrame.EXIT_ON_CLOSE)
  
  //////////////////////////////////////////////////////////////////////////////

  private val menu = new JPopupMenu()

  private def addMenuItem(name : String)(action : => Unit) = {
    val item = new JMenuItem(name)
    menu add item
    addActionListener(item) {
      action
    }
  }
  
  addMenuItem("New tab") { defaultNewTab }
  addMenuItem("New SMT-LIB tab") { defaultSMTNewTab }
  
  addMenuItem("Duplicate tab") {
    val i = tabbedPane.getSelectedIndex
    val currentTab = getEnabledPanel
    val oldTitle = tabbedPane getTitleAt i

    val tab = newPanel
    createdTabs = createdTabs + 1
    tabbedPane.addTab(oldTitle + " (b)", tab)

    tab.setInput(currentTab.inputField.getText, currentTab.file)
    tab.optionField setText currentTab.optionField.getText

    tab.inputField setCaretPosition 0
    tabbedPane setSelectedIndex (tabbedPane.getTabCount - 1)
  }
  
  addMenuItem("Close tab") {
    val tabToClose = getEnabledPanel
    if (tabToClose discardModifications "Close") {
      tabToClose.stopProver
      if (tabbedPane.getTabCount == 1)
        // make sure that there is at least one tab left
        defaultNewTab
      tabbedPane remove tabToClose
    }
  }
  
  //////////////////////////////////////////////////////////////////////////////
  // Loading and saving files
  
  menu.addSeparator
  
  lazy val loadFileChooser = new JFileChooser
  
  addMenuItem("Load ...") {
    loadFileChooser.showOpenDialog(frame) match {
      case JFileChooser.APPROVE_OPTION => loadFile(loadFileChooser.getSelectedFile)
      case _ => // nothing
    }
  }
  
  addMenuItem("Load in this tab ...") {
    if (getEnabledPanel discardModifications "Load") {
      loadFileChooser.showOpenDialog(frame) match {
        case JFileChooser.APPROVE_OPTION => {
          val tab = getEnabledPanel
          tab.stopProver

          val file = loadFileChooser.getSelectedFile
          for ((options, input) <- readFile(file)) {
            tab.setInput(input, Some(file))
            tab.optionField setText options
            tabbedPane.setTitleAt(tabbedPane.getSelectedIndex, file.getName)
          }
        }
        case _ => // nothing
      }
    }
  }
  
  def loadFile(file : File) : Unit =
    for ((options, input) <- readFile(file)) {
      newTabWithInput(file.getName, Some(file), options, input)
    }

  def readFile(file : File) : Option[(String, String)] = try {
    val reader = new java.io.BufferedReader (new java.io.FileReader(file))
    val options =
      if (file.getName endsWith ".smt2")
        "-inputFormat=smtlib"
      else if (file.getName endsWith ".p")
        "-inputFormat=tptp"
      else
        ""
    val input = asString {
      var str = reader.readLine
      while (str != null) {
        println(str)
        str = reader.readLine
      }
    }
    Some((options, input))
  } catch {
    case e : java.io.IOException => {
      JOptionPane.showMessageDialog(frame, "Error loading file: \n" + e.getMessage)
      None
    }
    case x : Throwable => throw x
  }
  
  lazy val saveFileChooser = new JFileChooser {
    override def approveSelection = {
      val file = getSelectedFile
      if (file.exists) {
        JOptionPane.showConfirmDialog(this,
                                      "Overwrite existing file?\n" + file.getName,
                                      getDialogTitle,
                                      JOptionPane.YES_NO_OPTION,
                                      JOptionPane.WARNING_MESSAGE) match {
          case JOptionPane.YES_OPTION =>
            super.approveSelection
          case _ => // nothing
        }
      } else {
        super.approveSelection
      }
    }
  }

  addMenuItem("Save as ...") {
    try {
    saveFileChooser.showSaveDialog(this) match {
      case JFileChooser.APPROVE_OPTION => {
        val file = saveFileChooser.getSelectedFile
        val i = tabbedPane.getSelectedIndex
        val currentTab = getEnabledPanel
        tabbedPane.setTitleAt(i, file.getName)
        val out = new java.io.FileOutputStream(file)
        Console.withOut(out) { Console.print(currentTab.inputField.getText) }
        out.close
        currentTab setFile Some(file)
      }
      case _ => // nothing
    }
    } catch {
      case e : java.io.IOException =>
        JOptionPane.showMessageDialog(frame, "Error saving file: \n" + e.getMessage)
      case x : Throwable => throw x
    }
  }
  
  //////////////////////////////////////////////////////////////////////////////

  {
    // register the shortcut F1
    this.getInputMap(JComponent.WHEN_ANCESTOR_OF_FOCUSED_COMPONENT)
        .put(KeyStroke.getKeyStroke("F1"), "theAction")
    this.getActionMap.put("theAction", new AbstractAction {
      def actionPerformed(e : ActionEvent) = getEnabledPanel.startOrStopProver
    })
  }

  //////////////////////////////////////////////////////////////////////////////

  private val tabbedPane = new JTabbedPane (SwingConstants.BOTTOM)
  add(tabbedPane)
  
  tabbedPane addMouseListener (new MouseAdapter {
    override def mouseClicked(e : MouseEvent) =
      if (e.getButton != MouseEvent.BUTTON1 && e.getClickCount == 1)
        menu.show(e.getComponent, e.getX, e.getY)
  })
  
  private def getEnabledPanel =
    tabbedPane.getSelectedComponent.asInstanceOf[PrincessPanel]
  
  private def newPanel : PrincessPanel =
    new PrincessPanel(menu) {
      def setRunning =
        (tabbedPane indexOfComponent this) match {
          case -1 => // nothing
          case i => {
            tabbedPane.setBackgroundAt(i, Color.red)
            tabbedPane.setToolTipTextAt(i, "Solving ...")
          }
        }
      def setFinished =
        (tabbedPane indexOfComponent this) match {
          case -1 => // nothing
          case i => {
            tabbedPane.setBackgroundAt(i, null)
            tabbedPane.setToolTipTextAt(i, null)
          }
        }
      def reload(f : File) : Unit =
        if (discardModifications("Reload")) {
          stopProver

          for ((_, input) <- readFile(f))
            setInput(input, Some(f))
        }
    }
  
  private def newTabWithInput(name : String, file : Option[File],
                              options : String, problem : String) = {
    val tab = newPanel
    createdTabs = createdTabs + 1
    tabbedPane.addTab(name, tab)
    tab.setInput(problem, file)
    tab.optionField setText options
    tabbedPane setSelectedIndex (tabbedPane.getTabCount - 1)
  }
  
  private def defaultNewTab =
    newTabWithInput("Problem " + (createdTabs + 1), None, "", asString {
      println("\\sorts {")
      println("  /* Declare sorts and algebraic data-types */")
      println("  ")
      println("}")
      println
      println("\\universalConstants {")
      println("  /* Declare universally quantified constants of the problem */")
      println("  ")
      println("}")
      println
      println("\\existentialConstants {")
      println("  /* Declare existentially quantified constants of the problem */")
      println("  ")
      println("}")
      println
      println("\\functions {")
      println("  /* Declare constants and functions occurring in the problem")
      println("   * (implicitly universally quantified).")
      println("   * The keyword \"\\partial\" can be used to define functions without totality axiom,")
      println("   * while \"\\relational\" can be used to define \"functions\" without functionality axiom. */")
      println("  ")
      println("}")
      println
      println("\\predicates {")
      println("  /* Declare predicates occurring in the problem")
      println("   * (implicitly universally quantified) */  ")
      println("  ")
      println("}")
      println
      println("\\problem {")
      println("  /* Problem to be proven. The implicit quantification is:")
      println("   *    \\forall <universalConstants>;")
      println("   *      \\exists <existentialConstants>;")
      println("   *        \\forall <functions/predicates>; ... */")
      println
      println("  true")
      println("}")
    })

  private def defaultSMTNewTab =
    newTabWithInput("Problem " + (createdTabs + 1), None, "-inputFormat=smtlib", asString {
     println("(set-logic AUFLIA)")
     println
     println(";; Set some options")
     println(";; The options affect all sub-sequent commands,")
     println(";; and can be specified more than once in a problem")
     println
     println(";; Translate boolean functions as predicates, or as functions?")
     println(";; (set-option :boolean-functions-as-predicates true) ; default: false")
     println
     println(";; Inline let-expressions, or encode them using quantifiers?")
     println(";; (set-option :inline-let false) ; default: true")
     println
     println(";; Inline define-fun functions, or encode them using axioms?")
     println(";; (set-option :inline-definitions false) ; default: true")
     println
     println(";; Introduce totality axiom for functions?")
     println(";; (set-option :totality-axiom true) ; default: false")
     println
     println(";; Introduce functionality axiom for functions?")
     println(";; (set-option :functionality-axiom false) ; default: true")
     println
     println(";; Prepare for generating interpolants?")
     println(";; (set-option :produce-interpolants true) ; default: false")
     println
     println(";; Declare functions and constants")
     println(";; (declare-fun f (Int) Int)")
     println(";; (declare-fun p (Int Int) Bool)")
     println(";; (declare-fun c () Int)")
     println
     println("(assert true)")
     println("(check-sat)")
     println("; (get-interpolants) ; also generate Craig interpolants?")
    })

  private var createdTabs = 0
  
  //////////////////////////////////////////////////////////////////////////////
  // Set up the example tabs

  newTabWithInput("ADTs", None, "", asString {
    println("/**")
    println(" * Example:")
    println(" * Problem over Algebraic Data-Types")
    println(" */")
    println
    println("/* Definition of Algebraic Data-Types */")
    println("\\sorts {")
    println("  Colour { red; green; blue; };")
    println("  Pair { Pair(int x, Colour c); };")
    println("}")
    println("")
    println("/* Definition of functions and variables of the problem */")
    println("\\functions {")
    println("  Pair inc(Pair p) { Pair(p.x + 1, p.c) };")
    println("  Pair p;")
    println("  int f(Pair);")
    println("}")
    println("")
    println("/* Problem to be proven */")
    println("\\problem {")
    println("  \\forall Pair p; f(p) = \\abs(p.x)")
    println("->")
    println("  f(p) != f(inc(p))")
    println("}")
  })

  newTabWithInput("Quantifiers", None, "", asString {
    println("/**")
    println(" * Example:")
    println(" * Problem in Presburger arithmetic with uninterpreted predicates")
    println(" */")
    println
    println("\\existentialConstants {")
    println("  /* Declare existentially quantified constants of the problem */")
    println
    println("  int A;")
    println("}")
    println
    println("\\predicates {")
    println("  /* Declare predicates occurring in the problem */  ")
    println
    println("  divides(int, int);")
    println("}")
    println
    println("\\problem {")
    println("  /* Problem to be proven. The implicit quantification is:")
    println("   *    \\exists <existentialConstants>; \\forall <predicates>; ... */")
    println
    println("     \\forall int x; divides(x, x)")
    println("  -> \\forall int x, y; (divides(x, y) -> divides(x, y+x) & divides(x, y-x))")
    println("  ->")
    println("     divides(A, 42) & divides(A, 49) & A > 1")
    println("}")
  })

  newTabWithInput("Interpolation", None, "", asString {
    println("/**")
    println(" * Example:")
    println(" * Craig interpolation problem in Presburger arithmetic")
    println(" */")
    println
    println("\\functions {")
    println("   int x, a, b, c;")
    println("}")
    println
    println("\\problem {")
    println("  /* Problem to be proven and interpolated */")
    println
    println("  \\part[cond]          (a-2*x = 0 & -a <= 0) &")
    println("  \\part[stmt1]         (2*b - a <=0 & -2*b + a -1 <=0) &")
    println("  \\part[stmt2]         c-3*b-1=0")
    println("                       ->")
    println("  \\part[assert]        c > a")
    println("}")
    println
    println("/* Interpolation specification */")
    println("\\interpolant {cond; stmt1, stmt2, assert}")
    println("\\interpolant {cond, stmt1; stmt2, assert}")
    println("\\interpolant {cond, stmt1, stmt2; assert}")
  })

  newTabWithInput("Quantifier elimination", None, "+mostGeneralConstraint", asString {
    println("/**")
    println(" * Quantifier elimination example:")
    println(" *")
    println(" * \"There a bound B such that every integer x >= B")
    println(" *  can be expressed as a non-negative linear combination")
    println(" *  of 7 and 8.\"")
    println(" *")
    println(" * The best such bound can be computed using")
    println(" * quantifier elimination. For this, variables are")
    println(" * declared within \\existentialConstants, and the option")
    println(" * +mostGeneralConstraint is used.")
    println(" */")
    println("")
    println("\\existentialConstants {")
    println("  int B;")
    println("}")
    println("")
    println("\\problem {")
    println("  \\forall int x; (x >= B -> \\exists nat y, z; x = 7*y + 8*z)")
    println("/**")
    println(" * Quantifier elimination determines that this formula is")
    println(" * equivalent to   B >= 42")
    println(" */")
    println("}")
  })

  newTabWithInput("SMT-LIB input", None, "-inputFormat=smtlib", asString{
    println("(set-logic AUFLIA)")
    println("(declare-fun a () Int)")
    println("(declare-fun p (Int) Bool)")
    println
    println("(assert (forall ((x Int)) (p (* 2 x))))")
    println("(assert (forall ((x Int)) (not (p (+ (* 2 x) 1)))))")
    println
    println("(assert (p a))")
    println("(assert (not (p (+ a 10))))")
    println
    println("(check-sat)")
  })

/*
  newTabWithInput("Array interpolation", None, "", asString {
    println("/**")
    println(" * Example:")
    println(" * Craig interpolation problem in the theory of arrays")
    println(" */")
    println
    println("\\functions {")
    println("  int x, y, z, ar;")
    println("  \\partial int select(int, int);")
    println("  \\partial int store(int, int, int);")
    println("}")
    println
    println("\\problem {")
    println("// Array axioms")
    println("  \\forall int ar, ind, val; {select(store(ar, ind, val), ind)}")
    println("    select(store(ar, ind, val), ind) = val")
    println("->")
    println("  \\forall int ar, ind1, ind2, val; {select(store(ar, ind1, val), ind2)}")
    println("    (ind1 != ind2 -> select(store(ar, ind1, val), ind2) = select(ar, ind2))")
    println("->")
    println
    println("  \\part[p0] (store(0, x, 1) = ar)")
    println("->")
    println("  \\part[p1] (select(ar, y) >= select(ar, x))")
    println("->")
    println("  \\part[p2] (z = select(ar, y)+1)")
    println("->")
    println("  \\part[p3] (z < 0)")
    println("->")
    println("  false")
    println("}")
    println
    println("\\interpolant {p0, p1; p2, p3}")
  })
  */

  newTabWithInput("SMT-LIB interpolation", None,
                  "-inputFormat=smtlib", asString{
    println(";")
    println("; Simple interpolation example")
    println(";")
    println
    println("(set-logic AUFLIA)")
    println
    println("(set-option :produce-interpolants true)")
    println
    println("(declare-fun f (Int) Int)")
    println("(declare-fun a () Int)")
    println("(declare-fun b () Int)")
    println
    println("(assert (> a (* b 2)))")
    println("(assert (< a (+ (* b 2) 2)))")
    println("(assert (> (f (- a 1)) (f (* 2 b))))")
    println
    println("(check-sat)")
    println("(get-interpolants)")
  })
  
  newTabWithInput("Incremental SMT-LIB", None,
                  "-inputFormat=smtlib +incremental", asString{
    println(";")
    println(";  Example from \"Interpolation in SMTLIB 2.0\", Juergen Christ, Jochen Hoenicke")
    println(";  (slightly modified)")
    println(";")
    println(";  The use of :named formulae for interpolation is currently only supported in")
    println(";  incremental mode")
    println(";")
    println("")
    println("(set-option :print-success false)")
    println("(set-option :produce-interpolants true)")
    println("(set-logic QF_UFLIA)")
    println("")
    println("(declare-fun x_1 () Int)")
    println("(declare-fun xm1 () Int)")
    println("(declare-fun x2 () Int)")
    println("(declare-fun res4 () Int)")
    println("(declare-fun resm5 () Int)")
    println("(declare-fun xm6 () Int)")
    println("(declare-fun x7 () Int)")
    println("(declare-fun res9 () Int)")
    println("(declare-fun resm10 () Int)")
    println("(declare-fun res11 () Int)")
    println("(assert (! (<= x_1 100) :named M1))")
    println("(assert (! (= xm1 (+ x_1 11)) :named M2))")
    println("(assert (! (> x2 100) :named S11))")
    println("(assert (! (= res4 (- x2 10)) :named S12))")
    println("(assert (! (and (= x2 xm1) (= resm5 res4)) :named S1RET))")
    println("(assert (! (= xm6 resm5) :named M3))")
    println("(assert (! (> x7 100) :named S21))")
    println("(assert (! (= res9 (- x7 10)) :named S22))")
    println("(assert (! (and (= x7 xm6) (= resm10 res9)) :named S2RET))")
    println("(assert (! (= res11 resm10) :named M4))")
    println("(check-sat) ; sat")
    println("")
    println("(assert (! (and (<= x_1 101) (distinct res11 91)) :named ERR))")
    println("(check-sat) ; unsat")
    println("")
    println("(echo \"\")")
    println("(echo \"01:\")")
    println("(get-interpolants)")
    println("")
    println("(echo \"\")")
    println("(echo \"02:\")")
    println("(get-interpolants (and M1 M2 S12 S11 S1RET) M3 (and S21 S22 S2RET) (and M4 ERR))")
    println("")
    println("(echo \"\")")
    println("(echo \"03:\")")
    println("(get-interpolants (and M1 M2 S12 S11 S1RET) (and S21 S22 S2RET) (and M4 ERR) M3)")
    println("")
    println("(echo \"\")")
    println("(echo \"04 (tree interpolants):\")")
    println("(get-interpolants M1 M2 (S11 S12) S1RET M3 (S21 S22) S2RET M4 ERR)")
  })

  newTabWithInput("TPTP input", None, "-inputFormat=tptp", asString{
    println("%------------------------------------------------------------------------------")
    println("% File     : GEG021=1 : TPTP v5.1.0. Released v5.1.0.")
    println("% Domain   : Arithmetic")
    println("% Problem  : Estimate distance between cities (one step)")
    println("% Version  : Especial.")
    println("% English  :")
    println("")
    println("% Refs     : [Wal10] Waldmann (2010), Email to Geoff Sutcliffe")
    println("% Source   : [Wal10]")
    println("% Names    :")
    println("")
    println("% Status   : Theorem")
    println("% Rating   : 0.67 v5.1.0")
    println("% Syntax   : Number of formulae    :   10 (   8 unit;   9 type)")
    println("%            Number of atoms       :   27 (  14 equality)")
    println("%            Maximal formula depth :   16 (   4 average)")
    println("%            Number of connectives :   15 (   0   ~;   0   |;  14   &)")
    println("%                                         (   0 <=>;   1  =>;   0  <=;   0 <~>)")
    println("%                                         (   0  ~|;   0  ~&)")
    println("%            Number of type conns  :    2 (   1   >;   1   *;   0   +;   0  <<)")
    println("%            Number of predicates  :   13 (  11 propositional; 0-2 arity)")
    println("%            Number of functors    :   22 (  20 constant; 0-2 arity)")
    println("%            Number of variables   :    6 (   0 sgn;   6   !;   0   ?)")
    println("%            Maximal term depth    :    3 (   2 average)")
    println("%            Arithmetic symbols    :   15 (   2 pred;    0 func;   13 numbers)")
    println("% SPC      : TFF_THM_EQU_ARI")
    println("")
    println("% Comments :")
    println("%------------------------------------------------------------------------------")
    println("tff(city_type,type,(")
    println("    city: $tType )).")
    println("")
    println("tff(d_type,type,(")
    println("    d: ( city * city ) > $int )).")
    println("")
    println("tff(kiel_type,type,(")
    println("    kiel: city )).")
    println("")
    println("tff(hamburg_type,type,(")
    println("    hamburg: city )).")
    println("")
    println("tff(berlin_type,type,(")
    println("    berlin: city )).")
    println("")
    println("tff(cologne_type,type,(")
    println("    cologne: city )).")
    println("")
    println("tff(frankfurt_type,type,(")
    println("    frankfurt: city )).")
    println("")
    println("tff(saarbruecken_type,type,(")
    println("    saarbruecken: city )).")
    println("")
    println("tff(munich_type,type,(")
    println("    munich: city )).")
    println("")
    println("tff(city_distance_1,conjecture,")
    println("    ( ( ! [X: city,Y: city] : d(X,Y) = d(Y,X)")
    println("      & ! [X: city,Y: city,Z: city] : $lesseq(d(X,Z),$sum(d(X,Y),d(Y,Z)))")
    println("      & ! [X: city] : d(X,X) = 0")
    println("      & d(berlin,munich) = 510")
    println("      & d(berlin,cologne) = 480")
    println("      & d(berlin,frankfurt) = 420")
    println("      & d(saarbruecken,frankfurt) = 160")
    println("      & d(saarbruecken,cologne) = 190")
    println("      & d(hamburg,cologne) = 360")
    println("      & d(hamburg,frankfurt) = 390")
    println("      & d(cologne,frankfurt) = 150")
    println("      & d(hamburg,kiel) = 90")
    println("      & d(hamburg,berlin) = 250")
    println("      & d(munich,frankfurt) = 300")
    println("      & d(munich,saarbruecken) = 360 )")
    println("   => $lesseq(d(cologne,berlin),500) )).")
    println("")
    println("%------------------------------------------------------------------------------")
  })

  tabbedPane setSelectedIndex 0
  
  //////////////////////////////////////////////////////////////////////////////

  frame.pack
  frame setVisible true
  
}

////////////////////////////////////////////////////////////////////////////////

abstract class PrincessPanel(menu : JPopupMenu)
                            (implicit ec : ExecutionContext) extends JPanel {

  import DialogUtil._

  def setRunning : Unit
  def setFinished : Unit

  def reload(f : File) : Unit

  //////////////////////////////////////////////////////////////////////////////
  
  setLayout(new BorderLayout)

  val inputField = new JTextArea
  val outputField = new JTextArea
  setupTextField(inputField)
  setupTextField(outputField)
  outputField setEditable false
  
  inputField addMouseListener (new MouseAdapter {
    override def mouseClicked(e : MouseEvent) =
      if (e.getButton == MouseEvent.BUTTON3 && e.getClickCount == 1)
        menu.show(e.getComponent, e.getX, e.getY)
  })

  inputField addMouseWheelListener (new MouseWheelZoomer (inputField))
  outputField addMouseWheelListener (new MouseWheelZoomer (outputField))

  private val scrolledInputField = vScrolled(inputField)
  private val scrolledOutputField = vScrolled(outputField)

  ss(scrolledInputField, 200, 700, 0, 350)
  ss(scrolledOutputField, 200, 700, 0, 250)
  
  private val splitPane = new JSplitPane(JSplitPane.VERTICAL_SPLIT,
                                         scrolledOutputField, scrolledInputField)

  add(splitPane, BorderLayout.CENTER)

  outputField setText asString {
    CmdlMain.printGreeting
//    println
//    CmdlMain.printOptions
  }

  var file : Option[File] = None

  var hasChanged : Boolean = false

  def setInput(newInput : String, newFile : Option[File]) = {
    inputField setText newInput
    inputField setCaretPosition 0
    setFile(newFile)
  }

  def setFile(newFile : Option[File]) = {
    file = newFile
    hasChanged = false
    reloadButton setEnabled file.isDefined
  }

  inputField.getDocument addDocumentListener (new DocumentListener {
    private def somethingChanged = {
      hasChanged = true
    }
    def insertUpdate(e : DocumentEvent) = somethingChanged
    def removeUpdate(e : DocumentEvent) = somethingChanged
    def changedUpdate(e : DocumentEvent) = somethingChanged
  })

  //////////////////////////////////////////////////////////////////////////////

  private val controlPanel = new JPanel
  controlPanel.setLayout(new BorderLayout)
  add(controlPanel, BorderLayout.SOUTH)

  private val leftPanel = new JPanel
  leftPanel setLayout (new FlowLayout (FlowLayout.LEADING, 2, 1))
  controlPanel.add(leftPanel, BorderLayout.WEST)
  
  private val menuButton = new JButton("File ...")
  leftPanel.add(menuButton)
  
  addActionListener(menuButton) {
    menu.show(menuButton, menuButton.getX, menuButton.getY)
  }

  private val reloadButton = new JButton("Reload")
  reloadButton setEnabled false
  leftPanel.add(reloadButton)
  
  addActionListener(reloadButton) {
    reload(file.get)
  }

  def discardModifications(verb : String) =
    if (hasChanged)
      JOptionPane.showConfirmDialog(this,
                                    "Tab contents have been modified.\n" +
                                    verb + " anyway?",
                                    "Discard modifications?",
                                    JOptionPane.YES_NO_OPTION,
                                    JOptionPane.WARNING_MESSAGE) match {
        case JOptionPane.YES_OPTION =>
          true
        case _ =>
          false
    } else {
      true
    }

  //////////////////////////////////////////////////////////////////////////////
  
  private val optionToolTipLocation = new Point (0, -400)

  leftPanel add Box.createRigidArea(new Dimension (8, 0))
  private val optionLabel = new JLabel("Options: ") {
    override def getToolTipLocation(e : MouseEvent) = optionToolTipLocation
  }
  leftPanel.add(optionLabel)
  
  val optionField = new JTextField {
    override def getToolTipLocation(e : MouseEvent) = optionToolTipLocation
  }
  controlPanel.add(optionField, BorderLayout.CENTER)
  
  private val toolTip = asString {
    println("<html><pre>")
    CmdlMain.printOptions
    println("</pre></html>")
  }

  /**
   * Make sure that the option tooltip stays open for a long time
   */
  private val optionToolTipMouseListener = new MouseAdapter {
    private var oldDismissDelay = ToolTipManager.sharedInstance.getDismissDelay

    override def mouseEntered(e : MouseEvent) = {
      oldDismissDelay = ToolTipManager.sharedInstance.getDismissDelay
      ToolTipManager.sharedInstance setDismissDelay 10000000
    }
    override def mouseExited(e : MouseEvent) = {
      ToolTipManager.sharedInstance setDismissDelay oldDismissDelay
    }
  }

  optionLabel addMouseListener optionToolTipMouseListener
  optionField addMouseListener optionToolTipMouseListener

  //////////////////////////////////////////////////////////////////////////////

  optionLabel setToolTipText toolTip
  optionField setToolTipText toolTip

  optionField addActionListener (new ActionListener {
    def actionPerformed(e : ActionEvent) = {
      if (!proverRunning)
        startProver
      }
    })
  
  //////////////////////////////////////////////////////////////////////////////

  private val goButton = new JButton("")
  setGoButtonGo
  controlPanel.add(goButton, BorderLayout.EAST)

  private def setGoButtonGo = {
    goButton setEnabled true
    goButton setText "Go!"
    goButton setForeground Color.BLUE
    goButton setToolTipText "Start proving (F1)"
  }
  
  private var proverRunning : Boolean = false
  private var proverStopRequested : Boolean = false
  
  def stopProver =
    if (proverRunning) {
      proverStopRequested = true
      goButton setEnabled false
      goButton setText "Stopping ..."
      goButton setToolTipText null
    }
  
  def startOrStopProver = 
    if (!proverRunning) startProver else stopProver
  
  addActionListener(goButton) { startOrStopProver }

  private def startProver : Unit = {
    val input = inputField.getText
    val reader = () => new java.io.BufferedReader (new java.io.StringReader(input))
    
    val settings = try {
      val initS =
        Param.INPUT_FORMAT.set(GlobalSettings.DEFAULT, Param.InputFormat.Princess)
      GlobalSettings.fromArguments(optionField.getText.split(' '), initS) _1
    } catch {
      case e : CmdlParser.UnknownArgumentException => {
        outputField setText asString {
          println(e.getMessage)
          println
          CmdlMain.printOptions
        }
        outputField setCaretPosition 0
        return
      }
    }

    outputField setText ""
    goButton setText "STOP"
    goButton setForeground Color.RED
    goButton setToolTipText "Stop proving (F1)"
    setRunning

    val proverOutputStream = new java.io.PipedOutputStream
    val logInputStream = new java.io.PipedInputStream(proverOutputStream)
    
    // start one thread for proving the problem
    proverRunning = true
    Future {
      proverStopRequested = false
      
      Console.withOut(proverOutputStream) {
        Console.withErr(if (Param.QUIET(settings))
                          CmdlMain.NullStream
                        else
                          proverOutputStream) {
          CmdlMain.proveProblems(settings, "", reader, proverStopRequested)(
                                 Param.INPUT_FORMAT(settings))
      }}
      
      proverOutputStream.close
      doLater {
        proverRunning = false
        setGoButtonGo
        setFinished
      }
    }
    
    // and another one for logging the output
    updateTextField(outputField, logInputStream)
  }
  
  //////////////////////////////////////////////////////////////////////////////

  splitPane setContinuousLayout true
  
}
