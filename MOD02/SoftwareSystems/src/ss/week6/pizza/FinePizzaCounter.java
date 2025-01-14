package ss.week6.pizza;

import java.util.LinkedList;
import java.util.List;
import java.util.concurrent.locks.Condition;
import java.util.concurrent.locks.ReentrantLock;

public class FinePizzaCounter {
    private ReentrantLock l1 = new ReentrantLock();
    private Condition wait_notfull = l1.newCondition();
    private Condition wait_isfull = l1.newCondition();

    private final List<Pizza> pizzas = new LinkedList<>();
    private static final int MAX_PIZZAS = 1;

    /**
     * Add a pizza to the counter.
     * @param pizza the pizza to add
     */
    public void addPizza(Pizza pizza) {
        // we can only have MAX_PIZZAS pizzas on the counter
        try {
            l1.lock();
            while (pizzas.size() >= MAX_PIZZAS) {
                try {
                    wait_notfull.await();
                } catch (InterruptedException e) {
                    throw new RuntimeException(e);
                }
            }
            pizzas.add(pizza);
            wait_isfull.signalAll();
        } finally {
            l1.unlock();
        }
    }

    /**
     * Take the first pizza from the counter.
     * @return the first pizza
     */
    public synchronized Pizza takePizza() {
        try {
            l1.lock();
            while (pizzas.isEmpty()) {
                try {
                    wait_isfull.await();
                } catch (InterruptedException e) {
                    throw new RuntimeException(e);
                }
            }

            Pizza result = pizzas.remove(0);
            wait_notfull.signalAll();
            return result;
        } finally {
            l1.unlock();
        }
    }
}