package ss.week6.pizza;

import java.io.BufferedReader;
import java.util.concurrent.locks.ReentrantLock;

/**
 * Pizza with pepperoni topping.
 */
public class Pizza {
    private int pepperoni = 0;
    ReentrantLock lock = new ReentrantLock();

    //@ private invariant pepperoni >= 0;

    /**
     * Add pepperoni to the pizza.
     */
    //@ ensures pepperoni == \old(pepperoni) + 1;
    public synchronized void addPepperoni() {
        pepperoni += 1;
    }
    public void addPepperoniLocked() {
        try {
            lock.lock();
            pepperoni += 1;
        }
        finally {
            lock.unlock();
        }
    }

    /**
     * Returns a textual representation of this pizza.
     * @return the textual representation
     */
    //@ pure;
    @Override
    public String toString() {
        return "pizza with " + pepperoni + " pepperoni";
    }
}
