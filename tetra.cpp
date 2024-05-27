#include <iostream>

extern "C" {
    double _TNP4test4main4main();
    double _TNP4test4main4sum2(double, double);
}

int main() {
    auto res = _TNP4test4main4main();
    std::cout << "sum2: " << _TNP4test4main4sum2(3, 4) << std::endl;
    std::cout << "main returned " << res << std::endl;
}
