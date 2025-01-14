package ss.week1;

import org.junit.jupiter.api.Disabled;
import org.junit.jupiter.api.Test;
import ss.week1.BrokenFibonacci;

import static org.junit.jupiter.api.Assertions.assertEquals;

public class BrokenFibonacciTest {
    @Test
    void fibonacciTest() {
        assertEquals(5, BrokenFibonacci.fibonacci(5));
        assertEquals(3, BrokenFibonacci.fibonacci(4));
        assertEquals(2, BrokenFibonacci.fibonacci(3));
        assertEquals(1, BrokenFibonacci.fibonacci(2));
        assertEquals(1, BrokenFibonacci.fibonacci(1));
        assertEquals(0, BrokenFibonacci.fibonacci(0));
        assertEquals(701408733, BrokenFibonacci.fibonacci(44));
    }
}
