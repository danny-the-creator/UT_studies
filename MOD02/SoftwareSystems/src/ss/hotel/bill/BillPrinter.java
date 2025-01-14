package ss.hotel.bill;

public interface BillPrinter {
    //@ requires text!= null;
    //@ ensures \result!= null;
    default String format(String text, double price){
        return String.format("%-20s%15.2f%n", text, price);
    }

    //@ requires text!= null;
    void printLine(String text, double price);
};

