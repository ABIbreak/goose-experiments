package iterator

func sliceIter[V any](s []V) func(yield func(int, V) bool) {
	return func(yield func(int, V) bool) {
		// TODO: i conflicts with the i declared in slice.for_range, should fix?
		// renamed from i to j for now
		for j, v := range s {
			if !yield(j, v) {
				return
			}
		}
	}
}

func isAscii(str []byte) bool {
	ret_val := true

	loop_body := func(i int, b byte) bool {
		_ = i
		if b >= 0x80 || b == 0x00 {
			ret_val = false
			return false
		}

		ret_val = true
		return true
	}

	iterator := sliceIter[byte](str)

	iterator(loop_body)

	return ret_val
}

func reverseSlice[V any](s []V) []V {
	rev_s := make([]V, len(s))

	loop_body := func(i int, v V) bool {
		rev_s[len(s) - 1 - i] = v

		return true
	}
	
	iterator := sliceIter[V](s)

	iterator(loop_body)

	return rev_s
}
