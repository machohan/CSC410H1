public class IntervalDriver {

    // Do not change or add annotations in this class!
    //@ public invariant this != null;
    
    /*@ requires i1 != null;
      @ requires i2 != null;
      @ ensures \result != null;
      @ ensures \result.low == \result.high
      @         || (\result.low == Math.min(i1.low, i2.low) 
      @         && \result.high == Math.max(i1.high, i2.high));
      @*/
    OpenInterval joinIntervals(OpenInterval i1, OpenInterval i2) {
	// Returns empty interval if i1 and i2 are non-overlapping.
	if (i1.getHigh() < i2.getLow() || i2.getHigh() < i1.getLow()) {
	    return new OpenInterval(0);
	}

	// Joins i1 and i2.
	int low = i1.getLow() < i2.getLow() ? i1.getLow() : i2.getLow();
	int high = i1.getHigh() > i2.getHigh() ? i1.getHigh() : i2.getHigh();
	return new OpenInterval(low, high);
    }
}

class OpenInterval{

    // Do not change implementations in this class!
    private /*@ spec_public @*/ int low;
    private /*@ spec_public @*/ int high;

    // Do not change this invariant!
    //@ invariant low <= high;

    // Creates an non-empty interval.
	// #TODO Problem 1.a ADD CONTRACT
	/*@ requires low <= high;
	  @ requires (* low is an integer *);
	  @ requires (* high is an integer *);
	  @ ensures this.low == low;
	  @ ensures this.high == high;
	  @*/
    public OpenInterval(int low, int high){
	this.low = low;
	this.high = high;
    }

    // Creates an empty interval.
    // #TODO Problem 1.a ADD CONTRACT
    /*@ requires (* x is an integer *);
	  @ ensures this.low == x;
	  @ ensures this.high == x;
	  @ ensures this.low == this.high;
	  @*/
    public OpenInterval(int x){
	this.low = x;
	this.high = x;
    }	
     
    // Returns lower bound.
    // #TODO Problem 1.b ADD CONTRACT
	/*@ requires this != null;
	  @ requires this.low <= this.high;
	  @	ensures (* \result is an integer *);
	  @*/
    public int getLow(){
	return this.low;
    }

    // Returns upper bound.
    // #TODO Problem 1.b ADD CONTRACT
    /*@ requires this != null;
	  @ requires this.high >= this.low;
	  @	ensures (* \result is an integer *);
	  @*/
    public int getHigh(){
	return this.high;
    }

    //@ requires x != null;
    // #TODO Problem 1.c ADD CONTRACT
	/*@ requires x != null;
	  @ requires (* x.low is an integer *);
	  @ requires (* x.high is an integer *);
	  @ requires \typeof(x) == \typeof(this);
	  @ ensures \result == true || \result == false;
	  @*/
    public /*@ pure */ boolean equals(OpenInterval x){
	return (this.low == x.low && this.high == x.high);
    }
}
