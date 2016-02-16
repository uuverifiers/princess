/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2009-2011 Philipp Ruemmer <ph_r@gmx.net>
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

package ap.basetypes;

import ap.util.{Debug, APTestCase, PlainRange, FilterIt, Logic}

class TestLeftistHeap(n : String) extends APTestCase(n) {

  def runTest = {
    n match {
      case "testInsertElements" => testInsertElements
      case "testInsertIterator" => testInsertIterator
      case "testInsertHeap" => testInsertHeap
      case "testRemoveAll" => testRemoveAll
      case "testLargeHeap" => testLargeHeap
      case "testHeapCollector" => testHeapCollector
      case "testFlatMap" => testFlatMap
    }
  }

  private val a = List(-34, 20, 60, 16, 7, 5, 20, 13)
  private val b = List(8, 1000, -1000)

  
   def testInsertElements = {
        var h = LeftistHeap.EMPTY_HEAP[Int]
        assertTrue("Empty heap should be empty",
                   h.isEmpty && h.size == 0)
        
        h.insert ( 1 )
        assertTrue("Empty heap should be empty",
                   h.isEmpty && h.size == 0)

        h = h.insert ( 1 )
        assertTrue("Heap should contain one element",
                   !h.isEmpty  && h.size  == 1 &&
                   h.findMin == 1)

        h = h.deleteMin
        assertTrue("Empty heap should be empty",
                   h.isEmpty  && h.size  == 0)

        h = h.insert ( 1 ).insert ( 2 )
        assertTrue("Heap should contain two elements",
                   !h.isEmpty  && h.size  == 2 &&
                   h.findMin   == 1 )
        h = h.deleteMin 
        assertTrue("Heap should contain one element",
                   !h.isEmpty  && h.size  == 1 &&
                   h.findMin   == 2)
        h = h.deleteMin 
        assertTrue("Empty heap should be empty",
                   h.isEmpty  && h.size  == 0)
  }

  private def sameElements[T] ( t0 : Iterator[T], t1 : Iterator[T] ) : Boolean =
    (Set.empty ++ t0) == (Set.empty ++ t1)

  private def checkHeap[HC <: HeapCollector[Int, HC]]
                       (elements : List[Int], h : LeftistHeap[Int, HC]) : Unit = {
        assertTrue ( "Heap has incorrect size",
                     h.size  == elements.size  &&
                     ( h.size  == 0 ) == h.isEmpty  )

        assertTrue ( "Unsorted heap iterator does not return the right elements",
                     sameElements ( h.unsortedIterator , elements.iterator  ) )

        {
        val sortedEls = h.sortedIterator.toList.toArray
        assertTrue("Elements returned by sorted iterator should be sorted",
                   Logic.forall(0, sortedEls.size - 1,
                                (i) => sortedEls(i) <= sortedEls(i+1)))
        }
        
        assertTrue ( "Sorted heap iterator does not return the right elements",
                     sameElements ( h.sortedIterator , elements.iterator  ) )

        var list : List[Int] = List()
        var hv = h
        while ( !hv.isEmpty  ) {
            list = (hv.findMin) :: list 
            hv = hv.deleteMin 
        }
        
        {
        val sortedEls = list.toArray
        assertTrue("Elements returned by findMin should be sorted",
                   Logic.forall(0, sortedEls.size - 1,
                                (i) => sortedEls(i) >= sortedEls(i+1)))
        }

        assertTrue ( "findMin does not return the right elements",
                     sameElements ( list.iterator , elements.iterator  ) )        
  }

  private def removeAll[T, HC <: HeapCollector[T, HC]]
                       (h : LeftistHeap[T, HC], elements : Iterator[T] )
                                 : LeftistHeap[T, HC] = {
    var res = h
    for (el <- elements) res = res.removeAll(el)
    res
  }

  def testInsertIterator = {
        var h = LeftistHeap.EMPTY_HEAP[Int]

        h = h.insertIt ( List[Int]().iterator  )
        checkHeap ( List[Int](), h )
        assertTrue("Empty heap should be empty",
                   h.isEmpty  && h.size  == 0)
        
        h = h.insertIt ( a.iterator  )        
        checkHeap ( a, h )

        h = h.insertIt ( a.iterator  )        
        checkHeap ( a ::: a, h )

        h = h.insertIt ( List[Int]().iterator  )
        checkHeap ( a ::: a, h )
        
        h = h.insertIt ( h.unsortedIterator  )
        checkHeap ( a ::: a ::: a ::: a , h )

        h = h.insertIt ( h.sortedIterator  )
        checkHeap ( a ::: a ::: a ::: a ::: a ::: a ::: a ::: a, h )
  }

  def testInsertHeap = {
        var h = LeftistHeap.EMPTY_HEAP[Int]

        h = h.insertIt ( a.iterator  )        
        checkHeap ( a, h )

        h = h.insertHeap ( LeftistHeap.EMPTY_HEAP[Int] )
        checkHeap ( a, h )

        h = h.insertHeap ( h )
        checkHeap ( a ::: a, h )

        h = h.insertHeap ( LeftistHeap.EMPTY_HEAP[Int].insert ( 123 ) )
        checkHeap ( 123 :: a ::: a, h )
  }

  def testRemoveAll = {
        var h = LeftistHeap.EMPTY_HEAP[Int]

        // Test removal of all elements (from empty heap)
        checkHeap ( List[Int](), removeAll( h, a.iterator  ) )

        h = h.insertIt ( a.iterator  )        
        checkHeap ( a, h )

        // Test removal of arbitrary elements
        checkHeap ( a.filterNot( (i) => (i == a.head)  ), h.removeAll( a.head  ) )

        // Test removal of all elements
        checkHeap ( List[Int](), removeAll( h, a.iterator  ) )

        // Test removal of non-existing elements
        assertEquals ( "Heap should not be different",
                       h, removeAll ( h, b.iterator  ) )
  }
 
  def testLargeHeap = {
        var h = LeftistHeap.EMPTY_HEAP[Int]
        val l = Debug.randoms(0, 1000000).take(1000).toList
        
        h = h.insertIt ( l.iterator )

        checkHeap ( l, h )
  }
  
  private class SetCollector(val conts : Set[Int])
                extends HeapCollector[Int, SetCollector] {
    def +(n : Int, hc : SetCollector) = new SetCollector(conts + n ++ hc.conts)
  }

  def testHeapCollector = {
    val empty = LeftistHeap.EMPTY_HEAP[Int, SetCollector](new SetCollector(Set.empty))
    val elements = Debug.randoms(0, 100).take(100).toList
    val filled = empty ++ elements
    
    checkHeap(elements, filled)
    assert(sameElements(filled.collector.conts.iterator, elements.iterator))
    
    var emptied = filled
    while (!emptied.isEmpty) {
      emptied = emptied.deleteMin
      assert(sameElements(emptied.collector.conts.iterator, emptied.unsortedIterator))
    }
  }

  def testFlatMap = {
    var h = LeftistHeap.EMPTY_HEAP[Int]
    val l = Debug.randoms(0, 1000000).take(1000).toList
    
    h = h.insertIt ( l.iterator )

    val h2 = h.flatMap((i) => Iterator.single(i+1), (h) => false)
    val h3 = h2.flatMap((i) => Iterator.single(i-1), (h) => false)
    
    checkHeap ( l, h3 )
  }
}
