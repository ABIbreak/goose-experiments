package iterator

func chanIter[V any](channel <-chan V) func(yield func(V) bool) {
	return func(yield func(V) bool) {
		// TODO: should channel closure be deferred?
		for v := range channel {
			if !yield(v) {
				return
			}
		}
	}
}

func collectChannel[V any](channel <-chan V) []V {
	s := make([]V, 0 /* random number */)

	loop_body := func(v V) bool {
		s = append(s, v)

		return true
	}

	iterator := chanIter[V](channel)

	iterator(loop_body)

	return s
}
