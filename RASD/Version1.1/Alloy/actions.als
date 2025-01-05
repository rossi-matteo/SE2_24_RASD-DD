module actions

open signatures

pred doNothing [] {}

// Predicate that models the preconditions and postconditions of a signUp action
pred signUp [] {
	some newUser : User' - User | newUser in User'
	and
	all newUser : User' - User | (
		(
			some o : Offer | 
				(generateRecommendation[o, o.offeringCompany, newUser] or 
				generateRecommendation[o, newUser, o.offeringCompany])
		)
		implies
		newUser in Student' - Student
	)
}

// Predicate that models the preconditions and postconditions of a postNewOffer action
pred postNewOffer [c : Company] {
	some newOffer : Offer' - Offer | newOffer in Offer'
	and
	all newOffer : Offer' - Offer | (
		no newOffer.(applicatingStudents') and
		(
			doNothing or
			some s : Student | 
				(generateRecommendation[newOffer, c, s] or generateRecommendation[newOffer, s, c])
		)
	)
}

// Predicate that models the preconditions and postconditions of a generateRecommendation action
pred generateRecommendation [o : Offer, recommended : Party, to : Party] {
	some newRecommendation : Recommendation' - Recommendation | (
		newRecommendation in Recommendation'
		and
		newRecommendation in (to.receivedRecommendations)'
		and
		newRecommendation.contextOffer' = o
		and
		newRecommendation.recommendedParty' = recommended
	)
	and
	all newRecommendation : Recommendation' - Recommendation | (
		newRecommendation.status' = UNHANDLED
	)
}

// Predicate that models the preconditions and postconditions of an acceptRecommendation action
pred acceptRecommendation[r : Recommendation] {
	r.status = UNHANDLED and (r.status)' = ACCEPTED 
	and
	(
		receivedRecommendations.r in Student implies (
			(
				receivedRecommendations.r in r.contextOffer.applicatingStudents 
				or
				applyToOffer[receivedRecommendations.r, r.contextOffer]
			)
		)
	)
	and
	(
		receivedRecommendations.r in Company implies (
			(some r1 : Recommendation | r1.contextOffer = r.contextOffer and r1 in r.recommendedParty.receivedRecommendations) 
			or
			generateRecommendation[r.contextOffer, r.contextOffer.offeringCompany, r.recommendedParty]
		)
	)
}

// Predicate that models the preconditions and postconditions of a rejectRecommendation action
pred rejectRecommendation[r : Recommendation] {
	r.status = UNHANDLED and (r.status)' = REJECTED
}

// Predicate that models the preconditions and postconditions of an applyToOffer action
pred applyToOffer [s : Student, o : Offer] {
	(s not in o.applicatingStudents) 
	and 
	(s in (o.applicatingStudents)') 
	and
	all r : (s.receivedRecommendations :> contextOffer.o) | 
		r.status = UNHANDLED implies (r.status)' = ACCEPTED
}
