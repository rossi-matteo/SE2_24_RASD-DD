module facts

open signatures
open actions

// Set of Users never loses elements: it either stays the same or some sign up has happened
fact consistentUsersSet {
	always (
		(User = User') 
		or
		(User in User' and signUp[])
	)
}

// Set of Offers never loses elements: it either stays the same or some company has published a new Offer
fact consistentOffersSet {
	always (
		(Offer = Offer')
		or
		(Offer in Offer' 
		and 
		all o : Offer' - Offer | postNewOffer[o.offeringCompany'])
	)
}

// Set of Recommendations never loses elements: it either stays the same or some Recommendation has been 
	// generated as a consequence of some other action
fact consistentRecommendationsSet {
	always (
		(Recommendation = Recommendation' 
		and 
		receivedRecommendations = receivedRecommendations') 
		or 
		(Recommendation in Recommendation' 
		and
		receivedRecommendations in receivedRecommendations'
		and 
		all r : Recommendation' - Recommendation | (
			generateRecommendation[r.contextOffer', r.recommendedParty', receivedRecommendations'.r]
			)
		)
	)
}

// A Recommendation can be generated only by specific actions
fact doNotGenerateRecommendationsSpontaneously {
	always (
		all r : Recommendation' |
			generateRecommendation[r.contextOffer', r.recommendedParty', receivedRecommendations'.r] 
			implies
			(
				(receivedRecommendations)'.r in Party' - Party 	// a signUp[] has happened
				or
				(r.contextOffer)' in Offer' - Offer	// a postNewOffer[...] has happened
				or
				one studRec : Company.receivedRecommendations | (		// an acceptRecommendation[...] has happened
					studRec.contextOffer = (r.contextOffer)' and
					studRec.recommendedParty = (receivedRecommendations)'.r and
					acceptRecommendation[studRec]
				)
			)
	)
}

// Relation of applications to Offers never loses elements: it either stays the same or some Student has applied to some Offer
fact consistentApplicationsRelation { 
	always (
		(applicatingStudents = applicatingStudents')
		or 
		(applicatingStudents in applicatingStudents' 
		and
		some s : Student, o : Offer | applyToOffer[s, o])
	)
}

// A change of status in a Recommendation can happen only if it has been accepted or rejected
fact doNotHandleRecommendationsSpontaneously {
	always (
		all r : Recommendation | (
			r.status = ACCEPTED implies once acceptRecommendation[r]
			and
			r.status = REJECTED implies once rejectRecommendation[r]
		)
	)
}
