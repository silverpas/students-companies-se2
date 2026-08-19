pred startSelectionExample {
	let sel = SelectionProcess | no sel.activeSelection and no sel.activeInternship
	some s : Student, i : Internship {
		some s.recommendedInternships
		addActiveSelection[s, i]
	}
}

run startSelectionExample for 1 but 3 User