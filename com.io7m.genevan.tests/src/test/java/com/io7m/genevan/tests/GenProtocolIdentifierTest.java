/*
 * Copyright © 2022 Mark Raynsford <code@io7m.com> https://www.io7m.com
 *
 * Permission to use, copy, modify, and/or distribute this software for any
 * purpose with or without fee is hereby granted, provided that the above
 * copyright notice and this permission notice appear in all copies.
 *
 * THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES
 * WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF
 * MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR ANY
 * SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
 * WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN
 * ACTION OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF OR
 * IN CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.
 */


package com.io7m.genevan.tests;

import com.io7m.genevan.core.GenProtocolIdentifier;
import com.io7m.genevan.core.GenProtocolVersion;
import net.jqwik.api.Arbitraries;
import net.jqwik.api.Arbitrary;
import net.jqwik.api.Combinators;
import net.jqwik.api.ForAll;
import net.jqwik.api.Property;
import net.jqwik.api.Provide;
import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.Test;

import static java.math.BigInteger.ZERO;
import static java.math.BigInteger.valueOf;

/**
 * Tests for protocol identifiers.
 */

public final class GenProtocolIdentifierTest
{
  @Provide
  private static Arbitrary<GenProtocolIdentifier> arbitraryProtocol()
  {
    final var bmaj =
      Arbitraries.bigIntegers()
        .greaterOrEqual(ZERO);
    final var bmin =
      Arbitraries.bigIntegers()
        .greaterOrEqual(ZERO);
    final var s =
      Arbitraries.strings()
        .alpha()
        .ofMinLength(1)
        .ofMaxLength(16);
    final var vs =
      Combinators.combine(bmaj, bmin)
        .as(GenProtocolVersion::new);

    return Combinators.combine(s, vs).as(GenProtocolIdentifier::new);
  }

  @Property
  public void testCompatibleReflexive(
    final @ForAll(value = "arbitraryProtocol") GenProtocolIdentifier x)
  {
    Assertions.assertTrue(x.isCompatibleWith(x));
  }

  @Property
  public void testCompatibleSymmetric(
    final @ForAll(value = "arbitraryProtocol") GenProtocolIdentifier x,
    final @ForAll(value = "arbitraryProtocol") GenProtocolIdentifier y)
  {
    Assertions.assertEquals(
      x.isCompatibleWith(y),
      y.isCompatibleWith(x)
    );
  }

  @Property
  public void testCompatibleTransitive(
    final @ForAll(value = "arbitraryProtocol") GenProtocolIdentifier x,
    final @ForAll(value = "arbitraryProtocol") GenProtocolIdentifier y,
    final @ForAll(value = "arbitraryProtocol") GenProtocolIdentifier z)
  {
    if (x.isCompatibleWith(y) && y.isCompatibleWith(z)) {
      Assertions.assertTrue(x.isCompatibleWith(z));
    }
  }
}
