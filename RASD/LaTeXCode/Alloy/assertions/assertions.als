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