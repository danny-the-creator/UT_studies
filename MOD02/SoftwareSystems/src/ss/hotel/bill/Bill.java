package ss.hotel.bill;

public class Bill {
    public BillPrinter billprinter;
    public double sum;
    public interface Item {
        double getPrice();
    }
    public Bill(BillPrinter billPrinter){
        this.billprinter = billPrinter;
    }
    //@ requires item!=null;
    //@ ensures this.sum == \old(this.sum) + item.getPrice();
    public void addItem(Item item){
        billprinter.printLine(item.toString(), item.getPrice());
        sum += item.getPrice();
    }
    public void close(){
        billprinter.printLine("total sum", sum);
    }
    public Double getSum() {
        return sum;
    }
}
