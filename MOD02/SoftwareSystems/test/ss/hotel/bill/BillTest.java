package ss.hotel.bill;
import org.junit.jupiter.api.*;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

public class BillTest {
    private StringBillPrinter stringBillPrinter;
    private Bill bill ;
    private Item apple, banana, plum, orange;


class Item implements Bill.Item {
    public String text;
    public double price;
    public Item(String text, double price) {
        this.text = text;
        this.price = price;
    }
    public double getPrice() {
        return price;
    }
    @Override
    public String toString() {
        return text;
    }
}
    @BeforeEach
    public void SetUp() {
        stringBillPrinter = new StringBillPrinter();
        bill = new Bill(stringBillPrinter);
        apple = new Item("apple", 10);
        banana = new Item("banana", 20);
        plum = new Item("plum", 20.25);
        orange = new Item("orange",50.50);

    }
    @Test
    public void testItem() {
        assertTrue(apple.toString().contains("apple"));
        assertEquals(10, apple.getPrice());

        assertTrue(plum.toString().contains("plum"));
        assertEquals(20.25, plum.getPrice());

        assertFalse(banana.toString().contains("beer"));
        assertEquals(50.50, orange.getPrice());
    }
    @Test
    public void testBillStart(){
        assertEquals(0, bill.getSum());
        assertFalse(stringBillPrinter.getResult().contains("total sum"));
        assertEquals(0,stringBillPrinter.allLines.length());
    }

    @Test
    public void testBill(){
        assertEquals(0, bill.getSum());
        bill.addItem(banana);
        assertEquals(20, bill.getSum());
        bill.addItem(orange);
        assertEquals(70.50, bill.getSum());
        bill.addItem(apple);
        assertEquals(80.50, bill.getSum());

        assertTrue(stringBillPrinter.allLines.contains("apple"));
        assertFalse(stringBillPrinter.allLines.contains("plum"));
        bill.close();
        assertTrue(stringBillPrinter.allLines.contains(bill.getSum().toString()));
        assertTrue(stringBillPrinter.getResult().contains("total sum"));
        System.out.println(stringBillPrinter.getResult());


    }

}
