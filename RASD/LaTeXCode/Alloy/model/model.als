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
