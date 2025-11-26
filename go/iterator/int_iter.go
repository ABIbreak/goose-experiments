package iterator

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

func factorial(n int) int {
	factorial := 1

	loop_body := func(i int) bool {
		factorial *= (i + 1)
		return true
	}

	iterator := intIter(n)

	iterator(loop_body)

	return factorial
}
