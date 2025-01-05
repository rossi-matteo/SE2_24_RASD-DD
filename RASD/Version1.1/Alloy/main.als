open signatures
open actions
open facts

pred initialize [] {
	#Student = 0
	#Company = 0
	#University = 0
	#Offer = 0
	#Recommendation = 0
}

pred System {
	initialize
	and
	always(
		(
			doNothing
			or
			signUp[]
			or
			(some c : Company | postNewOffer[c])
			or
			(some s : Student, o : Offer | applyToOffer[s, o])
			or
			(some r : Recommendation | acceptRecommendation[r])
			or
			(some r : Recommendation | rejectRecommendation[r])
		)
	)
}

pred largeStaticWorld {
	#Student = 6
	#Company = 4
	#University = 2
	#Offer = 5
	#Recommendation = 5
	#status.ACCEPTED = 2
	#status.REJECTED = 1
	#applicatingStudents = 6
}

run largeStaticWorld for 24 but 1..1 steps

pred exampleDynamicWorld {
	// World initialization, and some new Users sign up
	initialize and signUp[];

	// Two distinct Companies post some new Offers and at least one new Recommendation is generated
	#Student = 1 and #Company = 2 and #University = 1 and 
		some disj c1, c2 : Company | postNewOffer[c1] and postNewOffer[c2] and
			some o : Offer', s : Student, c : Company | generateRecommendation[o, s, c];

	// Some new Users sign up; a Company accepts a Recommendation, causing another one to be sent to the 
		// recommended Student
	signUp[] and #Company = 3 and #Offer = 2 and #Recommendation < 4 and
		some s : Student, r : Company.receivedRecommendations | 
			(no s.receivedRecommendations and no applicatingStudents.s and 
				r.recommendedParty = s and acceptRecommendation[r]);

	// A Student applies to an Offer spontaneously, without accepting a Recommendation; another one accepts
		// a Recommendation, so that they also apply to an Offer via that operation; a Recommendation gets
		// rejected; another Company without Offers posts an Offer
	some disj s1, s2 : Student | (
		(some o : Offer | applyToOffer[s1, o]) and
		(some r : s2.receivedRecommendations | acceptRecommendation[r])
	) and
	some r : Recommendation | rejectRecommendation[r]
	and
	some c : Company | no offeringCompany.c and postNewOffer[c];

	// Bound on the maximum # of instances (to avoid cluttered worlds, which would prevent the understanding
		// of what is happening)
	#User = 6 and #Offer = 3 and #Recommendation < 5
}

run exampleDynamicWorld for 10 but 5..6 steps
