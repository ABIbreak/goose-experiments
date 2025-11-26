package iterator

import (
	"reflect"
	"testing"
)

func TestFactorial0(t *testing.T) {
	if factorial(0) != 1 {
		t.Errorf(`0! should be 1!`)
	}
}

func TestFactorial7(t *testing.T) {
	if factorial(7) != 5040 {
		t.Errorf(`7! should be 5040!`)
	}
}

func TestIsAsciiEmpty(t *testing.T) {
	if !isAscii([]byte("")) {
		t.Errorf(`"" is an ASCII string!`)
	}
}

func TestIsAsciiTrue(t *testing.T) {
	if !isAscii([]byte("I_AM-an-aScIi-string!67")) {
		t.Errorf(`"I_AM-an-aScIi-string!67" is an ASCII string!`)
	}
}

func TestIsAsciiFalse(t *testing.T) {
	if isAscii([]byte("∃non∧sciiCharInthisString")) {
		t.Errorf(`"∃non∧sciiCharInthisString" is not an ASCII string!`)
	}
}

func TestReverseSliceEmpty(t *testing.T) {
	if !reflect.DeepEqual([]int{}, reverseSlice([]int{})) {
		t.Errorf(`[] is the reverse of itself!`)
	}
}

func TestReverseSlice0(t *testing.T) {
	s := []int{1, 2, 3, 4, 5, 6, 7}
	rev_s := []int{7, 6, 5, 4, 3, 2, 1}

	if !reflect.DeepEqual(rev_s, reverseSlice(s)) {
		t.Errorf(`[7 ... 0] was not reversed correctly!`)
	}
}