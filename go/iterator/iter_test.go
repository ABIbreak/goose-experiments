package iterator

import (
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
