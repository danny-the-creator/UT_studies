package ss.week2;

/**
 * This class records an amount of money as dollars and cents.
 */
public class DollarsAndCentsCounter {
    int a = 0;
    /**
     * Return the amount of getDollars.
     * @return the amount of getDollars
     */
    //@ ensures \result >= 0;
    //@ pure
    public int getDollars() {
        return a/100;
    }

    /**
     * Return the amount of cents.
     * @return the amount of cents
     */
    //@ ensures \result >= 0 && \result < 100;
    //@ pure
    public int getCents() {
        return a%100;
    }

    /**
     * Add the specified amount of dollars and cents to this counter.
     * @param dollars the amount of dollars to add
     * @param cents the amount of cents to add
     */
    /*@ ensures getDollars() * 100 + getCents() ==
          \old(getDollars() * 100 + getCents()) + dollars * 100 + cents;
      @ */
    public void add(int dollars, int cents) {
        a+= dollars * 100 + cents;
    }

    /**
     * Reset this counter to 0.
     */
    //@ ensures getDollars() == 0 && getCents() == 0;
    public void reset() {
        a=0;
    }
}
