//package iter
//package main
package iterator

//import (
//	"github.com/goose-lang/std"
// should push this into Perennial 
//	"iter"
//)

// func(yield func(V) bool) is the signature of iter.Seq[V]

func intIter(limit int) func(yield func(int) bool) {
	return func(yield func(int) bool) {
		for i := 0; i < limit; i++ {
			if !yield(i) {
				return
			}
		}
	}
}

/*
func intIter(limit int) func(yield func(int) bool) {
	temp_limit := limit
	return func(yield func(int) bool) {
		for i := 0; i < temp_limit; i++ {
			if !yield(i) {
				return
			}
		}
	}
}
*/

func bozo(i int) bool {
	return i > 6
}

func main() {
	intIter(5)(bozo)
}

