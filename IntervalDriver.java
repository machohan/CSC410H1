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
	// ADD CONTRACTS #TODO
	/*@ requires this.low != null;
	  @ requires low == integer;
	  @	requires high != null && high == integer;
	  @ requires low < high;
	  @*/
    public OpenInterval(int low, int high){
	this.low = low;
	this.high = high;
    }

    // Creates an empty interval.
	//ADD CONTRACTS #TODO
	/*@ requires x != null && x == integer;
	  @ ensures low == high;
	  @*/
    public OpenInterval(int x){
	this.low = x;
	this.high = x;
    }	
     
    // Returns lower bound.
	//ADD CONTRACTS #TODO
	/*@ requires this != null;
	  @	ensures \result != null;
	  @*/
    public int getLow(){
	return this.low;
    }

    // Returns upper bound.
	//ADD CONTRACTS #TODO
	/*@ requires this != null;
	  @ ensures \result != null;
	  @*/
    public int getHigh(){
	return this.high;
    }

    //@ requires x != null;
	//Complete CONTRACTS #TODO
	/*@ ensures \result == true || \result == false;
	  @ requires x != null;
	  @ requires x.low != null && x.high != null;
	  @ requires \typeof(x) == \typeof(this);
	  @*/
    public /*@ pure */ boolean equals(OpenInterval x){
	return (this.low == x.low && this.high == x.high);
    }
}
