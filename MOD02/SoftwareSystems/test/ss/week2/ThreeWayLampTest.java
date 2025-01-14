package ss.week2;
import static org.junit.jupiter.api.Assertions.assertEquals;

import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import ss.week2.ThreeWayLamp;
public class ThreeWayLampTest {
    static ThreeWayLamp lamp;
    @BeforeEach
    void init(){
        lamp = new ThreeWayLamp();
    }
    @Test
    void test1() {
        assertEquals(ThreeWayLamp.LampSettings.off, lamp.print());
    }
    @Test
    void test2() {
        assertEquals(ThreeWayLamp.LampSettings.off, lamp.print());
        lamp.next();
        assertEquals(ThreeWayLamp.LampSettings.low, lamp.print());
        lamp.next();
        assertEquals(ThreeWayLamp.LampSettings.medium, lamp.print());
        lamp.next();
        assertEquals(ThreeWayLamp.LampSettings.high, lamp.print());
        lamp.next();
        assertEquals(ThreeWayLamp.LampSettings.off, lamp.print());
    }
    @Test
    void test3() {
        lamp.change("superhigh");
        assertEquals(ThreeWayLamp.LampSettings.off, lamp.print());
        lamp.change("high");
        assertEquals(ThreeWayLamp.LampSettings.high, lamp.print());
    }
}
