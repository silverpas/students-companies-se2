abstract sig User {}

sig University extends User {
	enrolledStudents : set Student,
	feedback : set Feedback
}

sig Student extends User {
	curriculum : Curriculum,
	var recommendedInternships : set Internship
} {
	// every student is enrolled in exactly one university
	one u : University | this in u.enrolledStudents
	// recommend all internships that are satisfied
	all i : Internship | recommend[this, i] iff i in recommendedInternships
}

sig Curriculum {
	skills : set Skill,
	experience : set Experience
} {
	// every curriculum is associated with exactly one student
	one s : Student | this = s.curriculum
}

sig Company extends User {
	internships : set Internship
}

sig Internship {
	requiredSkills : set Skill,
	requiredExperience : set Experience,
	questionnaire : set Question,
	var recommendedStudents : set Student
} {
	// every internship is associated with exactly one company
	one c : Company | this in c.internships
	// recommend all the students that satisfy the requirements
	all s : Student | recommend[s, this] iff s in recommendedStudents
}

one sig SelectionProcess {
	var activeSelection : Student -> Internship,
	var activeInternship : Student lone -> lone Internship
}{
	// an active internship can't select new students
	all i : Internship |
		some activeInternship.i implies no activeSelection.i
}

sig Feedback {
	user : User,
	internship : Internship
} {
	// a university can NOT write a feedback
	user not in University
	// a user was in the internship or the company owns the internship
	once (
		user -> internship in SelectionProcess.activeInternship or
		internship in user.internships
	)
	// the internship is active
	one u : Student | u -> internship in SelectionProcess.activeInternship
}


sig Skill, Experience, Question {}

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

// ASSERTIONS

// a student is not enrolled in more than one university
noStudentsInMultipleUniversities : check {
	all disj u1, u2 : University | no (u1.enrolledStudents & u2.enrolledStudents)
} for 10

// universities cannot submit feedback
noUniversityFeedback : check {
	all f : Feedback |
		f.user not in University
} for 10

// every student has a personal curriculum 
noSameCurriculum : check {
	all disj s1, s2 : Student | s1.curriculum != s2.curriculum
} for 10

// companies doesn't share internships
noSameInternship : check {
	all disj c1, c2 : Company | no (c1.internships & c2.internships)
} for 10

// there are no students with more than one active internships
// and no internships active more than once
noMultipleActiveInternships : check {
	let active = SelectionProcess.activeInternship | 
		no i : Internship, s : Student |
			#(active.i) > 1 or #(s.active) > 1
} for 10

// every student is enrolled
allStudentsAreEnrolled : check {
	all s : Student | one u : University | s in u.enrolledStudents
} for 10

// the recommendation relationship is mutual and active only
// if the predicate is true
recommendationCheck : check {
	all s : Student, i : Internship |
		recommend[s, i] implies (s in i.recommendedStudents and i in s.recommendedInternships)
} for 10

recommendMutual : check {
	all s : Student, i : Internship |
		s in i.recommendedStudents iff i in s.recommendedInternships
} for 10

// if an internship is active it isn't suggested
dontSuggestUnavailableInternships : check {
	all i : Internship |
		some SelectionProcess.activeInternship.i implies not recommend[Student, i]
} for 10

// an internship cannot have bot active selection and be started
noBothSelectionAndActiveInternship : check {
	let sel = SelectionProcess | no i : Internship |
		some sel.activeSelection.i and some sel.activeInternship.i
} for 10

// EXAMPLES

// start selection
pred startSelectionExample {
	let sel = SelectionProcess | no sel.activeSelection and no sel.activeInternship
	some s : Student, i : Internship {
		some s.recommendedInternships
		addActiveSelection[s, i]
	}
}

run startSelectionExample for 1 but 3 User

// start internship
pred startInternshipExample {
	let sel = SelectionProcess | one sel.activeSelection and no sel.activeInternship
	some s : Student, i : Internship {
		some s.recommendedInternships
		addActiveInternship[s, i]
	}
}

run startInternshipExample for  1 but 3 User

// stop internship
pred stopInternshipExample {
	let sel = SelectionProcess | no sel.activeSelection and some sel.activeInternship
	some s : Student, i : Internship {
		removeActiveInternship[s, i]
	}
}

run stopInternshipExample for  1 but 3 User

// multiple active selection and one final internship
pred multipleActiveSelection {
	let sel = SelectionProcess.activeSelection |
		some disj s1, s2 : Student | one i : Internship | 
			s1 -> i in sel and
			s2 -> i in sel
	#(SelectionProcess.activeInternship) = 0
	some s : Student, i : Internship | addActiveInternship[s, i]
}

run multipleActiveSelection for 4 but 1 Question, 0 Experience, 0 Skill, 1 Internship
