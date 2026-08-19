pred stopInternshipExample {
	let sel = SelectionProcess | no sel.activeSelection and some sel.activeInternship
	some s : Student, i : Internship {
		removeActiveInternship[s, i]
	}
}

run stopInternshipExample for 1 but 3 User