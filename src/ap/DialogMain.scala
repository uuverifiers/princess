/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2009-2011 Philipp Ruemmer <ph_r@gmx.net>
 *
 * Princess is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * Princess is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with Princess.  If not, see <http://www.gnu.org/licenses/>.
 */

package ap;

import ap.parameters.{GlobalSettings, Param}
import ap.util.CmdlParser

import scala.collection.mutable.ArrayBuffer
import scala.actors.Actor._
import scala.actors.{Actor, TIMEOUT}

import javax.swing._
import java.awt.{BorderLayout, FlowLayout, Dimension, Font, Color, Point}
import java.awt.event.{ActionEvent, ActionListener, MouseAdapter,
                       MouseEvent, KeyEvent}

object DialogMain {
  
  def main(args : Array[String]) : Unit = {
    // since some of the actors in the dialog class use blocking file operations,
    // we have to disable the actor-fork-join stuff to prevent deadlocks
    sys.props += ("actors.enableForkJoin" -> "false")
    val dialog = new InputDialog
    // we assume that given arguments are files to be loaded
    for (s <- args)
      dialog loadFile (new java.io.File (s))
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

  def updateTextField(outputField : JTextArea, stream : java.io.InputStream) =
    actor {
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

}

////////////////////////////////////////////////////////////////////////////////

class InputDialog extends JPanel {

  import DialogUtil._
  
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
    val oldTitle = tabbedPane getTitleAt i

    val tab = newPanel
    createdTabs = createdTabs + 1
    tabbedPane.addTab(oldTitle + " (b)", tab)

    tab.inputField setText getEnabledPanel.inputField.getText
    tab.optionField setText getEnabledPanel.optionField.getText

    tab.inputField setCaretPosition 0
    tabbedPane setSelectedIndex (tabbedPane.getTabCount - 1)
  }
  
  addMenuItem("Close tab") {
    val tabToClose = getEnabledPanel
    tabToClose.stopProver
    if (tabbedPane.getTabCount == 1)
      // make sure that there is at least one tab left
      defaultNewTab
    tabbedPane remove tabToClose
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
  
  def loadFile(file : java.io.File) : Unit = try {
    val reader = new java.io.BufferedReader (new java.io.FileReader(file))
    val options =
      if (file.getName endsWith ".smt2") "-inputFormat=smtlib" else ""
    newTabWithInput(file.getName, options, asString {
      var str = reader.readLine
      while (str != null) {
        println(str)
        str = reader.readLine
      }
    })
  } catch {
    case e : java.io.IOException =>
      JOptionPane.showMessageDialog(frame, "Error loading file: \n" + e.getMessage)
    case x => throw x
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
        tabbedPane.setTitleAt(i, file.getName)
        val out = new java.io.FileOutputStream(file)
        Console.withOut(out) { Console.print(getEnabledPanel.inputField.getText) }
        out.close
      }
      case _ => // nothing
    }
    } catch {
      case e : java.io.IOException =>
        JOptionPane.showMessageDialog(frame, "Error saving file: \n" + e.getMessage)
      case x => throw x
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
      def setRunning = {
        val i = tabbedPane indexOfComponent this
        tabbedPane.setBackgroundAt(i, Color.red)
        tabbedPane.setToolTipTextAt(i, "Solving ...")
      }
      def setFinished = {
        val i = tabbedPane indexOfComponent this
        tabbedPane.setBackgroundAt(i, null)
        tabbedPane.setToolTipTextAt(i, null)
      }
    }
  
  private def newTabWithInput(name : String, options : String, problem : String) = {
    val tab = newPanel
    createdTabs = createdTabs + 1
    tabbedPane.addTab(name, tab)
    tab.inputField setText problem
    tab.inputField setCaretPosition 0
    tab.optionField setText options
    tabbedPane setSelectedIndex (tabbedPane.getTabCount - 1)
  }
  
  private def defaultNewTab =
    newTabWithInput("Problem " + (createdTabs + 1), "", asString {
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
    newTabWithInput("Problem " + (createdTabs + 1), "-inputFormat=smtlib", asString {
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
     println(";; Introduce totality axiom for functions?")
     println(";; (set-option :totality-axiom false) ; default: true")
     println
     println(";; Introduce functionality axiom for functions?")
     println(";; (set-option :functionality-axiom false) ; default: true")
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
  
  newTabWithInput("Arithmetic example", "", asString {
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

  newTabWithInput("Arithmetic interpolation example", "", asString {
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

  newTabWithInput("Array interpolation example", "", asString {
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
  
  newTabWithInput("SMT-LIB example", "-inputFormat=smtlib", asString{
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
  
  tabbedPane setSelectedIndex 0
  
  //////////////////////////////////////////////////////////////////////////////

  frame.pack
  frame setVisible true
  
}

////////////////////////////////////////////////////////////////////////////////

abstract class PrincessPanel(menu : JPopupMenu) extends JPanel {

  import DialogUtil._

  def setRunning : Unit
  def setFinished : Unit
  
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

  //////////////////////////////////////////////////////////////////////////////
  
  private val optionToolTipLocation = new Point (0, -640)

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
      if (currentProver == null)
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
  
  private var currentProver : Actor = null
  private var proverStopRequested : Boolean = false
  
  def stopProver =
    if (currentProver != null) {
      proverStopRequested = true
      goButton setEnabled false
      goButton setText "Stopping ..."
      goButton setToolTipText null
    }
  
  def startOrStopProver = 
    if (currentProver == null) startProver else stopProver
  
  addActionListener(goButton) { startOrStopProver }

  private def startProver : Unit = {
    val input = inputField.getText
    val reader = () => new java.io.StringReader(input)
    
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
    currentProver = actor {
      proverStopRequested = false
      
      Console.withOut(proverOutputStream) { Console.withErr(proverOutputStream) {
        CmdlMain.proveProblems(settings, List(("", reader)), proverStopRequested)
      }}
      
      proverOutputStream.close
      doLater {
        currentProver = null
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