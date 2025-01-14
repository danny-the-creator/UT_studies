package ss.hotel;

import ss.hotel.bill.Bill;
import ss.hotel.password.Password;

public class PricedSafe extends Safe implements Bill.Item {
    Password password = new Password();
    double price;
    public PricedSafe(double price){
        this.price = price;
    }

    @Override
    public double getPrice() {
        return price;
    }
    //@ requires pass != null;
    //@ ensures active == true ==> password.testWord(pass);
    public void activate(String pass){
        assert pass != null;
        if (password.testWord(pass)){
            active = true;
        }
    }
    @Override
    public void activate() {
        System.out.println("PasswordIsNeeded");
    }
    //@ requires pass != null;
    //@ ensures opened == true ==> password.testWord(pass) && isActive();
    public void open(String pass){
        assert pass != null;
        if (password.testWord(pass) && isActive()){
            opened = true;
        }
    }
    @Override
    public void open(){
        System.out.println("PasswordIsNeeded");
    }

    public Password getPassword(){
        return password;
    }

    @Override
    public String toString() {
        return "Safe ("+price+"euro)";
    }

    public static void main(String[] args) {
        PricedSafe ps = new PricedSafe(23);
        String password_ = null;
        ps.open(password_);
    }
}
