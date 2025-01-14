package ss.hotel.bill;

public class SysoutBillPrinter implements BillPrinter{

    public void printLine (String text, double price){
        System.out.print(format(text,price));
    }
    public static void main(String [] arg){
    BillPrinter printer = new SysoutBillPrinter();
        printer.printLine( "something1", 20.20);
        printer.printLine( "something2", 257.20);
        printer.printLine( "something3", 30.20);
        printer.printLine( "something4", 2944.20);

    }
}
