package ss.hotel;

import ss.hotel.bill.Bill;

public class PricedRoom extends Room implements Bill.Item {
    public double roomPrice;
    public PricedSafe safe;

    public PricedRoom(int number, double roomPrice, double safePrice) {
        super(number, new PricedSafe(safePrice));
        this.roomPrice = roomPrice;
    }

    public String toString() {
        return "Room" +this.number + " ("+roomPrice+" p/n)";
    }
    @Override
    public double getPrice() {
        return roomPrice;
    }
}
