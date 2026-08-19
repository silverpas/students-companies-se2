pred startInternshipExample {
	let sel = SelectionProcess | one sel.activeSelection and no sel.activeInternship
	some s : Student, i : Internship {
		some s.recommendedInternships
		addActiveInternship[s, i]
	}
}

run startInternshipExample for 1 but 3 User