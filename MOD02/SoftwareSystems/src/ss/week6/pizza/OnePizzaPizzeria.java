package ss.week6.pizza;

import java.util.concurrent.locks.Lock;

public class OnePizzaPizzeria {
    public static void main(String[] args) {
        Pizza pizza = new Pizza();
        PizzaChef chef1 = new PizzaChef(pizza);
        PizzaChef chef2 = new PizzaChef(pizza);
        Thread threadOne = new Thread(chef1);
        Thread threadTwo = new Thread(chef2);
        threadOne.start();
        threadTwo.start();
        try {
            threadOne.join();
        } catch (InterruptedException e) {
            throw new RuntimeException(e);
        }
        try {
            threadTwo.join();
        } catch (InterruptedException e) {
            throw new RuntimeException(e);
        }
        System.out.println(pizza.toString());


    }
}