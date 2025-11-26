package iterator

func sliceIter[V any](s []V) func(yield func(int, V) bool) {
	return func(yield func(int, V) bool) {
		for i, v := range s {
			if !yield(i, v) {
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
