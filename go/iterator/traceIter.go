package iterator

func sliceIter[V any](s []V) func(yield func(V) bool) {
	return func(yield func(V) bool) {
		for _, v := range s {
			if !yield(v) {
				return
			}
		}
	}
}

func isAscii(str []byte) bool {
	ret_val := true

	loop_body := func (b byte) bool {
		if (b >= 0x80 || b == 0x00) {
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
