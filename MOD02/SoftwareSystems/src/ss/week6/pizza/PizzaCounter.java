package ss.week6.pizza;

import java.util.LinkedList;
import java.util.List;

/**
 * Simulates a pizza counter with limited space.
 */
public class PizzaCounter {
    private final List<Pizza> pizzas = new LinkedList<>();
    private static final int MAX_PIZZAS = 1;
    //@ private invariant pizzas.size() >= 0 && pizzas.size()<= MAX_PIZZAS;
    /**
     * Add a pizza to the counter.
     * @param pizza the pizza to add
     */
    //@ ensures \old(pizzas.size()) < MAX_PIZZAS ==> pizzas.size() == \old(pizzas.size()) + 1;
    public synchronized void addPizza(Pizza pizza) {
        // we can only have MAX_PIZZAS pizzas on the counter
        while (pizzas.size() >= MAX_PIZZAS){
            try {
                wait();
            } catch (InterruptedException e) {
                throw new RuntimeException(e);
            }}
        pizzas.add(pizza);
        notifyAll();

    }

    /**
     * Take the first pizza from the counter.
     * @return the first pizza
     */
    //@ ensures \old(pizzas.size()) > 0 ==> pizzas.size() == \old(pizzas.size()) - 1 && \result== \old(pizzas).get(0);
    public synchronized Pizza takePizza() {
        while (pizzas.isEmpty()){
            try {
                wait();
            } catch (InterruptedException e) {
                throw new RuntimeException(e);
            }
        }

        Pizza result = pizzas.remove(0);
        notifyAll();
        return result;
    }
}
