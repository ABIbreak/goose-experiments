package iterator

func mapIter[K comparable, V comparable](m map[K]V) func(yield func(K, V) bool) {
	return func(yield func(K, V) bool) {
		for k, v := range m {
			if !yield(k, v) {
				return
			}
		}
	}
}

func mapDeepEqual[K comparable, V comparable](m1, m2 map[K]V) bool {
	if len(m1) != len(m2) {
		return false
	}

	ret_val := true

	loop_body := func(k1 K, v1 V) bool {
		v2, present := m2[k1]

		if !present || v1 != v2 {
			ret_val = false
			return false
		}

		return true
	}

	iterator := mapIter[K, V](m1)

	iterator(loop_body)

	return ret_val
}
