// a student fullfills all the internship requirement
pred recommend[s : Student, i : Internship] {
	let cv = s.curriculum {
		i.requiredSkills in cv.skills
		i.requiredExperience in cv.experience
	}
	// the internship is NOT active
	no SelectionProcess.activeInternship.i
	// the student has NOT participated yet
	not once (s -> i in SelectionProcess.activeInternship)
}

// a new active selection is addedd 
pred addActiveSelection [s : Student, i : Internship] {
	let sel = SelectionProcess.activeSelection, 
		proj = SelectionProcess.activeInternship
		{
			s -> i not in sel
			sel' = sel + s -> i
			proj' = proj
		}
	// the student has NOT started this internship
	not once (s -> i in SelectionProcess.activeInternship)
}

// an active selection is removed
pred removeActiveSelection [s : Student, i : Internship] {
	let sel = SelectionProcess.activeSelection, 
		proj = SelectionProcess.activeInternship 
		{
			s -> i in sel
			sel' = sel - s -> i
			proj' = proj
		}
}

// an internship is started after a selection
pred addActiveInternship [s : Student, i : Internship] {
	let sel = SelectionProcess.activeSelection,
		proj = SelectionProcess.activeInternship
		{
			s -> i in sel
			s -> i not in proj
			sel' = sel - Student -> i
			proj' = proj + s -> i	
		}
}

// an internship is stopped
pred removeActiveInternship [s : Student, i : Internship] {
	let sel = SelectionProcess.activeSelection,
		proj = SelectionProcess.activeInternship
		{
			s -> i in proj
			proj' = proj - s -> i
			sel' = sel
		}
}

pred noAction {
	let sel = SelectionProcess.activeSelection,
		proj = SelectionProcess.activeInternship
		{
			sel = sel'
			proj = proj'
		}
}

// the possible state's actions
fact transition {
	always 
	(
		some s : Student, i : Internship | 
			addActiveSelection[s, i] or 
			removeActiveSelection[s , i] or
			addActiveInternship[s, i] or 
			removeActiveInternship[s, i] or
			noAction
	)
}