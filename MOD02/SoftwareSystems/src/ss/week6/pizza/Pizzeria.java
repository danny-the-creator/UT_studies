package ss.week6.pizza;

/**
 * Represents a pizzeria.
 */
public class Pizzeria {
    private final FinePizzaCounter counter = new FinePizzaCounter();
    private static final int PIZZA_COUNT = 10; // pizzas per delivery person per chef
    private static final int DELIVERY_PERSON_COUNT = 2;
    private static final int CHEF_COUNT = 2;

    /**
     * Represent having pizza chefs bake pizzas
     */
    private void bakePizzas() {
        for (int i = 0; i < DELIVERY_PERSON_COUNT*PIZZA_COUNT; i++) {
            var pizza = new Pizza();
            new PizzaChef(pizza).run();
            counter.addPizza(pizza);
            System.out.printf("Baked pizza %d: %s%n", i, pizza);
        }
    }

    /**
     * Represents an overworked delivery person delivering pizzas
     */
    private void deliverPizzas() {
        for (int i = 0; i < CHEF_COUNT*PIZZA_COUNT; i++) {
            var pizza = counter.takePizza();
            System.out.printf("Delivering pizza %d: %s%n", i, pizza);
            // delivery is hard work and takes some time

            try {
                Thread.sleep(100);
            } catch (InterruptedException e) {
                // ignore, if we're interrupted, we're done anyway
            }
        }
    }

    /**
     * Runs this legal pizza operation.
     * @param args command line arguments, not used
     */
    public static void main(String[] args) {
        var pizzeria = new Pizzeria();
        for (int i = 0; i < CHEF_COUNT; i++) {
            new Thread(pizzeria::bakePizzas).start();
        }
        for (int i = 0; i < DELIVERY_PERSON_COUNT; i++) {
            new Thread(pizzeria::deliverPizzas).start();
        }
        // The threads continue to run, even though the main thread has finished.
    }
}
