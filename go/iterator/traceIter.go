package iterator

func isAscii(str []byte) bool {
	ret_val := true

	var loop_body func(int) bool = func (i int) bool {
		if (str[i] >= 0x80 || str[i] == 0x00) {
			ret_val = false
			return false
		}

		ret_val = true
		return true
	}

	iterator := intIter(len(str))

	iterator(loop_body)

	return ret_val
}
