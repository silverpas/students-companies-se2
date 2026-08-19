pred multipleActiveSelection {
	let sel = SelectionProcess.activeSelection |
		some disj s1, s2 : Student | one i : Internship | 
			s1 -> i in sel and
			s2 -> i in sel
	#(SelectionProcess.activeInternship) = 0
	some s : Student, i : Internship | addActiveInternship[s, i]
}

run multipleActiveSelection for 4 but 1 Question, 0 Experience, 0 Skill, 1 Internship