//package iter
//package main
package iterator

import (
//	"fmt"
//	"github.com/goose-lang/std"
// should push this into Perennial 
//	"iter"
)

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

func isAscii(str []byte) bool {
	ret_val := true

	loop_body := func (i int) bool {
		if (str[i] >= 0x80 || str[i] == 0x00) {
			ret_val = false
			return false
		}

		ret_val = true
		return true
	}

	intIter(len(str))(loop_body)

	return ret_val
}

func main() {
//	fmt.Println(isAscii([]byte("amongus")))
}

