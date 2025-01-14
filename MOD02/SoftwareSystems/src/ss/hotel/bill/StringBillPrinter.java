package ss.hotel.bill;

public class StringBillPrinter implements BillPrinter{
    String allLines = "";
    @Override
    public void printLine(String text, double price) {
        allLines += format(text, price);

    }
    public String getResult(){
        return allLines;
    }

    public static void main(String[] args) {
        StringBillPrinter pr = new StringBillPrinter();
        pr.printLine( "something1", 20.20);
        pr.printLine( "something2", 257.20);
        pr.printLine( "something3", 30.20);
        pr.printLine( "something4", 2944.20);
        System.out.println(pr.getResult());
    }
}
