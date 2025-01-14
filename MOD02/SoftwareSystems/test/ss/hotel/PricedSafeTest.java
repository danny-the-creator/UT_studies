package ss.hotel;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import ss.hotel.bill.Bill;

public class PricedSafeTest {

    private PricedSafe safe;
    private static final double PRICE = 6.36;
    private static final String PRICE_PATTERN = ".*6[.,]36.*";

    public String CORRECT_PASSWORD;
    public String WRONG_PASSWORD;


    @BeforeEach
    public void setUp() throws Exception {
        safe = new PricedSafe(PRICE);
        CORRECT_PASSWORD = safe.getPassword().getInitPass();
        WRONG_PASSWORD = CORRECT_PASSWORD + "WRONG";
        assertFalse(safe.isActive());
        assertFalse(safe.isOpened());
    }

    @Test
    public void testIsBillItem() throws Exception {
    	assertTrue(safe instanceof Bill.Item,
    			"safe should be an instance of Bill.Item.");
        assertEquals(PRICE, safe.getPrice(), 0,
        		"GetPrice should return the price of the safe.");
    }
    @Test
    public void testGetPrice(){
        assertEquals(PRICE, safe.getPrice());
    }
    @Test
    public void testToString(){
        assertTrue(safe.toString().contains("Price of the Safe: "+PRICE));

    }
    @Test
    public void testActivationTrue(){
        safe.activate(CORRECT_PASSWORD);
        assertTrue(safe.isActive());
        assertFalse(safe.isOpened());
    }
    @Test
    public void testActivationFalse(){
        safe.activate(WRONG_PASSWORD);
        assertFalse(safe.isActive());
        assertFalse(safe.isOpened());
    }
    @Test
    public void testOpenDeactivatedTrue(){
        assertFalse(safe.isActive());
        safe.open(CORRECT_PASSWORD);
        assertFalse(safe.isActive());
        assertFalse(safe.isOpened());
    }
    @Test
    public void testOpenDeactivatedFalse(){
        assertFalse(safe.isActive());
        safe.open(WRONG_PASSWORD);
        assertFalse(safe.isActive());
        assertFalse(safe.isOpened());
    }
    @Test
    public void testOpenActivated(){
        safe.activate(CORRECT_PASSWORD);
        assertTrue(safe.isActive());
        safe.open(WRONG_PASSWORD);
        assertFalse(safe.isOpened());
        safe.open(CORRECT_PASSWORD);
        assertTrue(safe.isActive());
        assertTrue(safe.isOpened());
    }
    @Test
    public void testCloseActivated(){
        safe.activate(CORRECT_PASSWORD);
        safe.open(CORRECT_PASSWORD);
        assertTrue(safe.isOpened());
        safe.close();
        assertFalse(safe.isOpened());
        assertTrue(safe.isActive());
    }
    @Test
    public void testCloseDeactivated(){
        assertFalse(safe.isActive());
//        assertFalse(safe.isOpened());
        safe.close();
        assertFalse(safe.isOpened());
        assertFalse(safe.isActive());
    }
}
